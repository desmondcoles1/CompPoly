import CompPoly.Fields.Binary.ClMulFast

/-!
# Benchmark harness for fast carry-less multiplication

## How to run
From the repo root:
  lake exe benchFastMul

Lake compiles this file (and everything it imports) into a native binary at
`.lake/build/bin/benchFastMul`, then runs it. `lake exe` always uses the
compiled binary — never the interpreter — so timing results are meaningful.

## What is benchmarked

### Full B256 pipeline
Each benchmark calls the multiply 100000 times on 256-bit inputs and measures
total wall time. The inputs are converted to/from `B256` (= `BitVec 256` = a
GMP big integer) on every iteration, so conversion overhead is included.

- `benchRef`          : original `clMul` — a `Finset.fold` over all 256 bit positions
- `benchFast`         : `clMulFast`      — C-backed Karatsuba (fastest, includes B256↔U256 conversion)
- `benchPure`         : `clMulFast_pure` — pure Lean 4-bit window Karatsuba (no C)
- `benchSampleGenB256`: sample generation overhead only (no multiply) — subtract from above

### U256 hot path
Stays in U256 throughout, skipping B256/GMP entirely.

- `benchU256`         : `clMul256K`      — C-backed Karatsuba
- `benchU256Pure`     : `clMul256K_pure` — pure Lean Karatsuba
- `benchSampleGenU256`: U256 sample generation overhead only — subtract from above

### 64-bit micro-benchmarks
Isolate just the 64×64-bit base multiply, operating directly on `UInt64` values.
A single 256×256 Karatsuba calls the base multiply 9 times, so these numbers
multiply up when reasoning about the full pipeline.

- `microClMul64`     : `clMul64`          — pure Lean, 4-bit window (16 steps)
- `microClMul64Spec` : `clMul64_fast_spec` — pure Lean, bit-by-bit loop (64 steps)
- `microClMul64C`    : `clMul64_fast_c`   — bare C FFI call (lower bound)
- `microSampleGen64` : 64-bit sample generation overhead only — subtract from above

## Timers
B256 benchmarks use `IO.monoMsNow` (milliseconds) — totals are in the seconds range
so ms resolution is sufficient. U256 and micro-benchmarks use `IO.monoNanosNow`
(nanoseconds) and report both total ns and ns/iter, since individual operations
are in the single-digit nanosecond range.

## Key insight from results
`B256 = BitVec 256 = Lean Nat = GMP big integer`. Every operation on a `B256`
heap-allocates a ~256-bit GMP object (~50–200 ns each). The bottleneck in the
full pipeline is NOT the arithmetic — it is the GMP allocations in `toU256` /
`ofU256`. The U256 hot path (`benchU256`) removes this overhead and is ~200×
faster than the reference.
-/

-- Bring all definitions from ClMulFast into scope without full qualification.
-- e.g. `clMulFast` instead of `BinaryField.clMulFast.clMulFast`.
open BinaryField.clMulFast

-- All benchmark code lives in this namespace to avoid polluting the top level.
namespace BinaryField.clMulFast.Bench

-- Number of multiply iterations per benchmark. 100000 gives stable ms-level
-- timings for the B256 benchmarks, and enough samples for ns/iter precision
-- on the faster U256 and micro-benchmarks.
def iters : Nat := 100000
-- Number of cases for the correctness check. 100000 gives good coverage cheaply.
def checkIters : Nat := 100000

-- The reference implementation is defined locally here rather than imported from
-- Common.lean. This matters: if `BinaryField.clMul` is later replaced by a fast
-- path, the correctness check would become vacuous (fast vs fast = always equal).
-- Keeping a private copy ensures we always compare against the naive algorithm.
private def clMul_ref (a b : B256) : B256 :=
  -- For each bit position i in 0..255: if bit i of `a` is set, XOR in `b` shifted
  -- left by i. This is polynomial multiplication over GF(2) done term by term.
  (Finset.univ : Finset (Fin 256)).fold BitVec.xor 0
    (fun i => if a.getLsb i then b <<< i.val else 0)

-- Sample inputs for the full B256 benchmarks.
-- Four UInt64 multiplications chain together so all 256 bits are populated —
-- important because the reference clMul is O(popcount(a)), and inputs with
-- many zero high bits would artificially favour the reference.
-- `ofU256` assembles the four 64-bit limbs into a single BitVec 256.
private def sampleA (i : Nat) : B256 :=
  let x : UInt64 := UInt64.ofNat i * 0x9e3779b97f4a7c15 + 0x1234567890abcdef
  let y : UInt64 := x * 0x6c62272e07bb0142 + 0x62b821756295c58d
  let z : UInt64 := y * 0x9e3779b97f4a7c15 + x
  let w : UInt64 := z * 0x6c62272e07bb0142 + y
  ofU256 ⟨x, y, z, w⟩

private def sampleB (i : Nat) : B256 :=
  let x : UInt64 := UInt64.ofNat i * 0xc2b2ae3d27d4eb4f + 0xfedcba0987654321
  let y : UInt64 := x * 0x9e3779b97f4a7c15 + 0x1234567890abcdef
  let z : UInt64 := y * 0x6c62272e07bb0142 + x
  let w : UInt64 := z * 0x9e3779b97f4a7c15 + y
  ofU256 ⟨x, y, z, w⟩

/-- Run `checkIters` correctness checks comparing both fast implementations against
    the local reference. Throws an IO error if any mismatch is found. -/
def checkCorrectness : IO Unit := do
  let mut mismatches := 0
  for i in [0:checkIters] do
    let a := sampleA i
    -- Offset b's index by 7 so a and b are not the same value (avoids trivial inputs).
    let b := sampleB (i + 7)
    let ref := clMul_ref a b
    if clMulFast a b != ref then
      IO.println s!"clMulFast mismatch at i={i}"
      mismatches := mismatches + 1
    if clMulFast_pure a b != ref then
      IO.println s!"clMulFast_pure mismatch at i={i}"
      mismatches := mismatches + 1
  if mismatches == 0 then
    IO.println s!"correctness check passed ({checkIters} cases, both implementations)"
  else
    throw <| IO.userError s!"{mismatches} mismatches found"

/-- Directly compare the Lean spec (`clMul64_fast_spec`) against the C function
    (`clMul64_fast_c`) on `checkIters` 64-bit input pairs.

    This is an empirical test of C correctness. We cannot prove in Lean that the C
    code is correct (Lean has no semantics for C). Instead, `@[implemented_by]`
    in ClMulFast.lean tells the runtime to substitute the C function for the spec,
    and this test checks that substitution is safe. -/
def checkClMul64 : IO Unit := do
  let mut mismatches := 0
  for i in [0:checkIters] do
    let a : UInt64 := UInt64.ofNat i * 0x9e3779b97f4a7c15 + 1
    let b : UInt64 := UInt64.ofNat i * 0xc2b2ae3d27d4eb4f + 1
    let spec := clMul64_fast_spec a b
    let c    := clMul64_fast_c    a b
    if spec != c then
      IO.println s!"clMul64 FFI mismatch at i={i}: spec=({spec.lo},{spec.hi}) c=({c.lo},{c.hi})"
      mismatches := mismatches + 1
  if mismatches == 0 then
    IO.println s!"clMul64 FFI check passed ({checkIters} cases)"
  else
    throw <| IO.userError s!"{mismatches} FFI mismatches"

/-- Check correctness on structured edge cases with known or algebraically-verifiable
    outputs. Tests both `clMulFast` (C-backed) and `clMulFast_pure` (pure Lean).

    ## Categories

    **Zero / identity** — exact expected outputs, no reference needed.

    **Single-bit products** — x^k · x^j = x^(k+j) in GF(2)[x], truncated to 256 bits:
      `(1 <<< k) * (1 <<< j) = if k+j < 256 then 1 <<< (k+j) else 0`
    Tested at and around every 64-bit limb boundary (63/64, 127/128, 191/192, 254/255).
    These are the exact inputs that stress Karatsuba's inter-limb carry propagation —
    a single misplaced bit in the assembly of z0/z1/z2 terms will show up here.

    **Adversarial inputs** — ten specific B256 values designed to hit degenerate
    cases in the Karatsuba structure. See inline comments for details.

    **Commutativity** — a · b = b · a, checked on all pairs of adversarial inputs
    and also verified against the reference.

    **Distributivity** — a · (b XOR c) = (a · b) XOR (a · c), checked on a
    representative subset of adversarial inputs.

    **Squaring structure** — in GF(2)[x], a² = ∑ aᵢ x^(2i), so odd bit positions
    in a² are always 0. A strong algebraic invariant that catches wrong products. -/
def checkEdgeCases : IO Unit := do
  -- Use an IO.Ref so the helper closures below can share the failure count.
  let failures ← IO.mkRef (0 : Nat)

  let fail (msg : String) : IO Unit := do
    IO.println s!"FAIL {msg}"
    failures.modify (· + 1)

  -- Check fast and pure against a precomputed expected value.
  let expect (tag : String) (a b expected : B256) : IO Unit := do
    let fast := clMulFast a b
    let pure := clMulFast_pure a b
    if fast != expected then
      fail s!"[{tag}] (fast): got {fast.toNat}, want {expected.toNat}"
    if pure != expected then
      fail s!"[{tag}] (pure): got {pure.toNat}, want {expected.toNat}"

  -- Check fast and pure agree with the local reference implementation.
  let vsRef (tag : String) (a b : B256) : IO Unit := do
    let ref  := clMul_ref a b
    let fast := clMulFast a b
    let pure := clMulFast_pure a b
    if fast != ref then
      fail s!"[{tag}] (fast vs ref): got {fast.toNat}, want {ref.toNat}"
    if pure != ref then
      fail s!"[{tag}] (pure vs ref): got {pure.toNat}, want {ref.toNat}"

  let max : B256 := ~~~ (0 : B256)

  -- ── Zero ──────────────────────────────────────────────────────────────────────
  expect "0*0"   0 0 0
  expect "0*1"   0 1 0
  expect "1*0"   1 0 0
  expect "0*max" 0 max 0
  expect "max*0" max 0 0

  -- ── Multiplicative identity (1 = x^0) ────────────────────────────────────────
  -- In GF(2)[x], 1 · b = b for all b.
  expect "1*1"   1 1 1
  expect "1*max" 1 max max
  expect "max*1" max 1 max

  -- ── Single-bit products: x^k · x^j = x^(k+j) ────────────────────────────────
  -- `clMul` truncates to 256 bits: products of degree ≥ 256 overflow to 0.
  -- Tested at and around every 64-bit limb boundary. These are the sharpest stress
  -- tests for Karatsuba: a single off-by-one in the limb assembly will fail here.
  let limbBoundaryBits : List Nat :=
    [0, 1, 62, 63,        -- bottom and top of limb 0
     64, 65,              -- just across the limb 0/1 boundary
     126, 127, 128, 129,  -- limb 1/2 boundary
     190, 191, 192, 193,  -- limb 2/3 boundary
     254, 255]            -- top of limb 3 (products here mostly overflow)
  for k in limbBoundaryBits do
    for j in limbBoundaryBits do
      let a : B256 := (1 : B256) <<< k
      let b : B256 := (1 : B256) <<< j
      let expected : B256 := if k + j < 256 then (1 : B256) <<< (k + j) else 0
      expect s!"(1<<{k})*(1<<{j})" a b expected

  -- ── Adversarial inputs ────────────────────────────────────────────────────────
  -- Ten B256 values chosen to exercise degenerate Karatsuba cases:
  --
  --   allOnes / altA / altB   : dense inputs; every limb populated
  --   limb0..limb3            : exactly one 64-bit limb nonzero; tests that the
  --                             Karatsuba z0/z2 terms are placed in the right words
  --   msbOnly                 : only the MSB of each limb set; checks MSB carry-out
  --                             across limb boundaries
  --   loEqHi                  : lo128 = hi128, so (lo XOR hi) = 0; the Karatsuba
  --                             cross-term argument becomes 0, making z1 = z0 XOR z2
  --   loXorHiMax              : lo128 XOR hi128 = all-ones; maximises the cross-term
  --                             input, stressing z1 computation
  let allOnes    := max
  let altA       := ofU256 ⟨0xAAAAAAAAAAAAAAAA, 0xAAAAAAAAAAAAAAAA, 0xAAAAAAAAAAAAAAAA, 0xAAAAAAAAAAAAAAAA⟩
  let altB       := ofU256 ⟨0x5555555555555555, 0x5555555555555555, 0x5555555555555555, 0x5555555555555555⟩
  let limb0      := ofU256 ⟨0xFFFFFFFFFFFFFFFF, 0, 0, 0⟩
  let limb1      := ofU256 ⟨0, 0xFFFFFFFFFFFFFFFF, 0, 0⟩
  let limb2      := ofU256 ⟨0, 0, 0xFFFFFFFFFFFFFFFF, 0⟩
  let limb3      := ofU256 ⟨0, 0, 0, 0xFFFFFFFFFFFFFFFF⟩
  let msbOnly    := ofU256 ⟨0x8000000000000000, 0x8000000000000000, 0x8000000000000000, 0x8000000000000000⟩
  let loEqHi     := ofU256 ⟨0xDEADBEEFCAFE1234, 0x0BADCAFE12345678, 0xDEADBEEFCAFE1234, 0x0BADCAFE12345678⟩
  let loXorHiMax := ofU256 ⟨0xAAAAAAAAAAAAAAAA, 0xBBBBBBBBBBBBBBBB, 0x5555555555555555, 0x4444444444444444⟩
  let adversarial : Array B256 :=
    #[allOnes, altA, altB, limb0, limb1, limb2, limb3, msbOnly, loEqHi, loXorHiMax]

  -- ── Commutativity: a · b = b · a ─────────────────────────────────────────────
  -- Checked on all pairs of adversarial inputs; also verified against the reference.
  for a in adversarial do
    for b in adversarial do
      vsRef "adversarial" a b
      if clMulFast a b != clMulFast b a then
        fail s!"[commutativity/fast] a*b ≠ b*a"
      if clMulFast_pure a b != clMulFast_pure b a then
        fail s!"[commutativity/pure] a*b ≠ b*a"

  -- ── Distributivity: a · (b XOR c) = (a · b) XOR (a · c) ─────────────────────
  let distribA  : Array B256 := #[allOnes, limb0, limb3, msbOnly]
  let distribBC : Array B256 := #[0, allOnes, altA, altB, limb0, limb3]
  for a in distribA do
    for b in distribBC do
      for c in distribBC do
        if clMulFast a (b ^^^ c) != clMulFast a b ^^^ clMulFast a c then
          fail s!"[distributivity/fast] a*(b XOR c) ≠ a*b XOR a*c"
        if clMulFast_pure a (b ^^^ c) != clMulFast_pure a b ^^^ clMulFast_pure a c then
          fail s!"[distributivity/pure] a*(b XOR c) ≠ a*b XOR a*c"

  -- ── Squaring structure in GF(2)[x] ───────────────────────────────────────────
  -- (∑ aᵢ xⁱ)² = ∑ aᵢ x^(2i): all exponents in the square are even, so odd bit
  -- positions in the low 256 bits of a² are always 0. This is a strong algebraic
  -- invariant — a wrong Karatsuba assembly almost certainly violates it.
  let oddBits : B256 :=
    ofU256 ⟨0xAAAAAAAAAAAAAAAA, 0xAAAAAAAAAAAAAAAA, 0xAAAAAAAAAAAAAAAA, 0xAAAAAAAAAAAAAAAA⟩
  let sqInputs : Array B256 := #[
    1, max, altA, altB, limb0, limb1, limb2, limb3, msbOnly, loEqHi,
    ofU256 ⟨0x1234567890abcdef, 0xfedcba9876543210, 0xdeadbeefcafe1234, 0x0102030405060708⟩
  ]
  for a in sqInputs do
    if clMulFast a a &&& oddBits != 0 then
      fail s!"[squaring/fast] odd bits set in a², a={a.toNat}"
    if clMulFast_pure a a &&& oddBits != 0 then
      fail s!"[squaring/pure] odd bits set in a², a={a.toNat}"

  -- ── Result ────────────────────────────────────────────────────────────────────
  let n ← failures.get
  if n == 0 then
    IO.println "edge case check passed"
  else
    throw <| IO.userError s!"{n} edge case failures"

-- `acc` XORs all results together so the compiler cannot eliminate the loop body
-- as dead code. It is always printed so the compiler cannot eliminate it as a
-- dead store either.

/-! ## Full B256 pipeline benchmarks (millisecond timer)

These include B256↔U256 conversion (= GMP allocation) on every iteration. -/

def benchRef : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut acc : B256 := 0
  for i in [0:iters] do
    acc := acc ^^^ clMul_ref (sampleA i) (sampleB i)
  let t1 ← IO.monoMsNow
  IO.println s!"reference clMul (Finset.fold):      {t1 - t0} ms  acc={acc.toNat}"

def benchFast : IO Unit := do
  -- clMulFast is defined as `BinaryField.clMul` in Lean (so proofs are trivial),
  -- but at runtime the compiler substitutes `clMulFast_impl` via @[implemented_by].
  -- clMulFast_impl does: toU256 → clMul256K (Karatsuba) → ofU256.
  let t0 ← IO.monoMsNow
  let mut acc : B256 := 0
  for i in [0:iters] do
    acc := acc ^^^ clMulFast (sampleA i) (sampleB i)
  let t1 ← IO.monoMsNow
  IO.println s!"C-backed clMulFast (Karatsuba):     {t1 - t0} ms  acc={acc.toNat}"

def benchPure : IO Unit := do
  -- Same structure as benchFast but uses the pure Lean Karatsuba (clMul64 base).
  let t0 ← IO.monoMsNow
  let mut acc : B256 := 0
  for i in [0:iters] do
    acc := acc ^^^ clMulFast_pure (sampleA i) (sampleB i)
  let t1 ← IO.monoMsNow
  IO.println s!"pure Lean clMulFast (4-bit window): {t1 - t0} ms  acc={acc.toNat}"

/-- Measures the cost of B256 sample generation alone (no multiply).
    Subtract this from `benchFast`/`benchPure` to isolate multiply cost. -/
def benchSampleGenB256 : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut acc : B256 := 0
  for i in [0:iters] do
    acc := acc ^^^ sampleA i ^^^ sampleB i
  let t1 ← IO.monoMsNow
  IO.println s!"B256 sample gen overhead:           {t1 - t0} ms  acc={acc.toNat}"

/-! ## U256 hot-path benchmarks (nanosecond timer)

Inputs stay as U256 throughout — no B256/GMP allocation at any point.
These measure arithmetic cost alone. -/

-- Shared U256 sample generator used by both hot-path benchmarks below.
private def sampleU256a (i : Nat) : U256 :=
  let a : UInt64 := UInt64.ofNat i * 0x9e3779b97f4a7c15 + 1
  ⟨a, a * 2 + 1, a * 3 + 2, a * 5 + 3⟩

private def sampleU256b (i : Nat) : U256 :=
  let b : UInt64 := UInt64.ofNat i * 0xc2b2ae3d27d4eb4f + 1
  ⟨b, b * 2 + 1, b * 3 + 2, b * 5 + 3⟩

-- Fold all four U256 words into one UInt64 for a compact acc display.
private def u256checksum (v : U256) : UInt64 := v.w0 ^^^ v.w1 ^^^ v.w2 ^^^ v.w3

def benchU256 : IO Unit := do
  -- Uses clMul256K: C-backed Karatsuba (clMul64_fast_c as base).
  let t0 ← IO.monoNanosNow
  let mut acc : U256 := ⟨0, 0, 0, 0⟩
  for i in [0:iters] do
    acc := acc ^^^ clMul256K (sampleU256a i) (sampleU256b i)
  let t1 ← IO.monoNanosNow
  let ns := t1 - t0
  IO.println s!"U256 C-backed  (no B256 conversion): {ns} ns  ({ns / iters} ns/iter)  acc={u256checksum acc}"

def benchU256Pure : IO Unit := do
  -- Same hot path as benchU256 but uses clMul256K_pure: pure Lean Karatsuba
  -- (clMul64 4-bit window as base, no C). Comparing this to benchU256 isolates
  -- the cost of the C base multiply vs the pure Lean base multiply.
  let t0 ← IO.monoNanosNow
  let mut acc : U256 := ⟨0, 0, 0, 0⟩
  for i in [0:iters] do
    acc := acc ^^^ clMul256K_pure (sampleU256a i) (sampleU256b i)
  let t1 ← IO.monoNanosNow
  let ns := t1 - t0
  IO.println s!"U256 pure Lean (no B256 conversion): {ns} ns  ({ns / iters} ns/iter)  acc={u256checksum acc}"

/-- Measures the cost of U256 sample generation alone (no multiply).
    Subtract from `benchU256`/`benchU256Pure` to isolate Karatsuba cost. -/
def benchSampleGenU256 : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc : U256 := ⟨0, 0, 0, 0⟩
  for i in [0:iters] do
    acc := acc ^^^ sampleU256a i ^^^ sampleU256b i
  let t1 ← IO.monoNanosNow
  let ns := t1 - t0
  IO.println s!"U256 sample gen overhead:            {ns} ns  ({ns / iters} ns/iter)  acc={u256checksum acc}"

/-! ## Micro-benchmarks: 64-bit base multiply only (nanosecond timer)

These isolate just the innermost multiply in the Karatsuba tree.
A single 256×256 multiply calls the base multiply 9 times, so these numbers
multiply up when reasoning about the full pipeline. -/

-- Deterministic 64-bit inputs. UInt64 arithmetic wraps mod 2^64 automatically.
private def sample64a (i : Nat) : UInt64 := UInt64.ofNat i * 0x9e3779b97f4a7c15 + 1
private def sample64b (i : Nat) : UInt64 := UInt64.ofNat i * 0xc2b2ae3d27d4eb4f + 1

def microClMul64 : IO Unit := do
  -- 4-bit window: processes 4 bits of `a` per step → 16 steps instead of 64.
  -- Pure Lean, no C. The `r.lo` and `r.hi` fields are the low/high 64 bits of
  -- the 128-bit product.
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := 0
  for i in [0:iters] do
    let r := clMul64 (sample64a i) (sample64b i)
    acc := acc ^^^ r.lo ^^^ r.hi
  let t1 ← IO.monoNanosNow
  let ns := t1 - t0
  IO.println s!"[micro] clMul64 pure Lean 4-bit:     {ns} ns  ({ns / iters} ns/iter)  acc={acc}"

def microClMul64Spec : IO Unit := do
  -- Bit-by-bit loop: 64 steps, one per bit of `a`. This is the Lean spec that
  -- mirrors the C loop exactly — used as the proof target for C correctness.
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := 0
  for i in [0:iters] do
    let r := clMul64_fast_spec (sample64a i) (sample64b i)
    acc := acc ^^^ r.lo ^^^ r.hi
  let t1 ← IO.monoNanosNow
  let ns := t1 - t0
  IO.println s!"[micro] clMul64_fast_spec (64-step):  {ns} ns  ({ns / iters} ns/iter)  acc={acc}"

def microClMul64C : IO Unit := do
  -- Direct C FFI call: the tightest possible 64×64 multiply.
  -- Shows the absolute lower bound — any Lean overhead on top of this is
  -- the cost of the Karatsuba glue code and struct field access.
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := 0
  for i in [0:iters] do
    let r := clMul64_fast_c (sample64a i) (sample64b i)
    acc := acc ^^^ r.lo ^^^ r.hi
  let t1 ← IO.monoNanosNow
  let ns := t1 - t0
  IO.println s!"[micro] clMul64_fast_c (bare C):      {ns} ns  ({ns / iters} ns/iter)  acc={acc}"

/-- Measures the cost of 64-bit sample generation alone (no multiply).
    Subtract from micro-benchmarks to isolate multiply cost. -/
def microSampleGen64 : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := 0
  for i in [0:iters] do
    acc := acc ^^^ sample64a i ^^^ sample64b i
  let t1 ← IO.monoNanosNow
  let ns := t1 - t0
  IO.println s!"[micro] 64-bit sample gen overhead:   {ns} ns  ({ns / iters} ns/iter)  acc={acc}"

-- Entry point for the benchmark namespace. Called by `main` below.
def main : IO Unit := do
  IO.println s!"iters={iters}  checkIters={checkIters}"
  IO.println ""
  -- Correctness checks first: fail fast before wasting time on benchmarks.
  checkCorrectness
  checkClMul64
  checkEdgeCases
  IO.println ""
  IO.println "--- full B256 pipeline (ms) ---"
  benchRef
  benchFast
  benchPure
  benchSampleGenB256
  IO.println ""
  IO.println "--- U256 hot path, no B256/GMP conversion (ns) ---"
  benchU256
  benchU256Pure
  benchSampleGenU256
  IO.println ""
  IO.println "--- 64-bit base multiply, micro (ns) ---"
  microClMul64
  microClMul64Spec
  microClMul64C
  microSampleGen64

end BinaryField.clMulFast.Bench

-- Top-level `main` required by Lake to produce an executable.
-- Lake looks for exactly this definition when compiling a `lean_exe` target.
-- Everything above is in a namespace; this unwraps it at the top level.
def main : IO Unit := BinaryField.clMulFast.Bench.main
