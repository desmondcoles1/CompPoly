import Std
import CompPoly.Fields.Binary.Common

/-!
# Fast carry-less multiplication over GF(2)[x] / (x²⁵⁶)

## Background
Carry-less multiplication (clMul) is polynomial multiplication over GF(2): coefficients
are bits, addition is XOR, and there is no carry between bit positions. It underlies
binary field arithmetic used in error-correcting codes, hashing (GHASH/GCM), and
zero-knowledge proof systems.

The reference implementation `BinaryField.clMul` in `Common.lean` is a `Finset.fold`
over all 256 bit positions — correct but slow (~53 µs per 256×256 multiply).

This file provides fast implementations that reduce that to ~8 µs (pure Lean) or ~0.3 µs
(C-backed, U256 hot path).

## Strategy: Karatsuba decomposition + native UInt64 limbs

### Step 1 — represent 256-bit values as four UInt64 limbs (U256)
`B256 = BitVec 256 = Lean Nat` — every operation heap-allocates a GMP big integer.
`U256` is a plain Lean structure with four `UInt64` fields; all arithmetic is on native
64-bit machine words with no allocation.

### Step 2 — fast 64×64 base multiply
Two options:
- `clMul64`           : pure Lean, 4-bit window (16 steps). No C, usable in proofs.
- `clMul64_fast`      : C-backed 64-bit loop (`clMul64.c`). Fastest at runtime.
Both return a 128-bit result as `U128`.

### Step 3 — Karatsuba decomposition
Karatsuba reduces n×n multiplications to 3 sub-multiplications (vs the naïve 4).
Applied twice:
  256×256 → 3 × (128×128)  via `clMul256K`
  128×128 → 3 × (64×64)    via `clMul128K`
Total: 9 base multiplies instead of 16.

Karatsuba identity (over any ring, including GF(2)[x]):
  (a_lo + a_hi·xⁿ)(b_lo + b_hi·xⁿ)
    = z0 + (z0 ⊕ z1 ⊕ z2)·xⁿ + z2·x²ⁿ
where z0 = a_lo·b_lo, z2 = a_hi·b_hi, z1 = (a_lo⊕a_hi)·(b_lo⊕b_hi).
(Addition = XOR because we are in GF(2)[x].)

### Step 4 — @[implemented_by] design pattern
`clMulFast` is *defined* as `BinaryField.clMul a b` in Lean. This makes the
top-level correctness theorem `clMulFast_eq_clMul` trivially `rfl` — no proof needed.
At runtime, the compiler substitutes `clMulFast_impl` (the fast path) via
`@[implemented_by]`. The open proof obligation is that `clMulFast_impl` actually
computes the same function — captured by the intermediate `*_correct` lemmas below.

## Proof obligations (all currently `sorry`'d)
1. `ofU256_toU256`          : B256 → U256 → B256 roundtrip
2. `toU256_ofU256`          : U256 → B256 → U256 roundtrip
3. `clMul64_correct`        : 4-bit window base case
4. `clMul64_fast_spec_correct` : bit-loop spec base case
5. `clMul128K_correct`      : Karatsuba 128×128, follows from (4)
6. `clMul256K_correct`      : Karatsuba 256×256, follows from (5)
7. `clMulFast_impl_correct` : full pipeline, follows from (1) + (6)

The C backend (`clMul64.c`) cannot be formally verified in Lean. Its correctness
is checked empirically by `BenchForFastMul.checkClMul64`.
-/

namespace BinaryField
namespace clMulFast

/-! ## Data types

`U128` and `U256` replace `BitVec 128` / `BitVec 256` for all hot-path arithmetic.
Using Lean structures with `UInt64` fields means field access and XOR compile to
single machine instructions, with no GMP allocation. -/

/-- 128-bit value as two native 64-bit words. `lo` holds bits 0–63, `hi` holds bits 64–127. -/
structure U128 where
  lo : UInt64
  hi : UInt64
deriving Repr, DecidableEq, Inhabited

/-- 256-bit value as four native 64-bit words, least-significant first. -/
structure U256 where
  w0 : UInt64  -- bits 0..63
  w1 : UInt64  -- bits 64..127
  w2 : UInt64  -- bits 128..191
  w3 : UInt64  -- bits 192..255
deriving Repr, DecidableEq, Inhabited

-- XOR instances let us write `a ^^^ b` for both types directly.
instance : HXor U128 U128 U128 := ⟨fun a b => ⟨a.lo ^^^ b.lo, a.hi ^^^ b.hi⟩⟩
instance : HXor U256 U256 U256 :=
  ⟨fun a b => ⟨a.w0 ^^^ b.w0, a.w1 ^^^ b.w1, a.w2 ^^^ b.w2, a.w3 ^^^ b.w3⟩⟩

/-- Low 128 bits of a U256 (words 0 and 1). -/
def U256.lo128 (v : U256) : U128 := ⟨v.w0, v.w1⟩
/-- High 128 bits of a U256 (words 2 and 3). -/
def U256.hi128 (v : U256) : U128 := ⟨v.w2, v.w3⟩

/-! ## Shift helpers (used by the pure Lean 4-bit window)

Lean's `UInt64` shift operators saturate (shifting by ≥ 64 gives 0), so we don't
need to guard those, but we do need to handle the 128-bit shift in two parts. -/

/-- Shift a U128 left by `s` bits (0 ≤ s < 128).

    WARNING: only correct for `s < 128`. For `64 ≤ s < 128` the `u.hi` word
    is silently dropped: its bits would land in positions `64 + s ≥ 128`, which
    overflow the 128-bit result. That is the right thing to do only when the
    caller guarantees `u.hi = 0` or doesn't need those bits. For the general
    case (`u.hi ≠ 0`, `64 ≤ s < 128`) the result is incorrect.
    This is safe here because `shiftLeftU128` is only called from the `clMul64`
    loop with shifts `4 * n` for `n ∈ {0, ..., 15}`, so `s ≤ 60 < 64`. -/
def shiftLeftU128 (u : U128) (s : Nat) : U128 :=
  if h0 : s = 0 then
    u
  else if h1 : s < 64 then
    -- Low word shifts up; the bits that overflow lo spill into hi.
    let s64 : UInt64 := UInt64.ofNat s
    ⟨u.lo <<< s64, (u.hi <<< s64) ^^^ (u.lo >>> (64 - s64))⟩
  else
    -- s ≥ 64: lo moves entirely into hi (shifted by s - 64); hi overflows and is dropped.
    -- NOTE: incorrect if u.hi ≠ 0; see warning above. Not reached in the 4-bit window
    -- (max shift = 4×15 = 60).
    ⟨0, u.lo <<< UInt64.ofNat (s - 64)⟩

/-- Shift a UInt64 left by `s` bits, widening the result to U128.
    Used to build the precomputed table in `clMul64`.

    WARNING: only correct for `s ∈ {0, 1, ..., 63}`. For `s ≥ 65`:
    - `64 - s64` underflows as `UInt64` (wraps to `2^64 - (s - 64)`),
      so `b >>> (64 - s64)` silently produces 0 instead of `b >>> (64 - s)`.
    - Lean shifts `UInt64` by `s % 64`, so `b <<< s64` gives `b <<< (s % 64)`
      rather than 0 for the low word.
    The result for `s ≥ 64` is wrong. This is safe only because the sole
    caller (`clMul64`) uses `s ∈ {0, 1, 2, 3}`. -/
def shiftLeftU64ToU128 (b : UInt64) (s : Nat) : U128 :=
  if s = 0 then
    ⟨b, 0⟩
  else
    let s64 : UInt64 := UInt64.ofNat s
    -- Low bits of b stay in lo after shift; high bits spill into hi.
    -- NOTE: requires s < 64; see warning above.
    ⟨b <<< s64, b >>> (64 - s64)⟩

/-! ## Base multiply 1: pure Lean 4-bit window

Instead of processing one bit of `a` per step (64 steps), we process 4 bits (one nibble)
per step (16 steps). Before the loop, we precompute all 16 possible products of a nibble
value (0–15) with `b`. Each product is just a subset-XOR of the four basic shifts of `b`.

This is safe to use in proofs (no opaque C functions). -/

/-- 64×64 carry-less multiply using a 4-bit window. Returns a 128-bit product.
    The 16 precomputed values t0..t15 are all XOR-combinations of b shifted by 0,1,2,3 bits,
    corresponding to which subset of the four low bits is set in a nibble value. -/
def clMul64 (a b : UInt64) : U128 :=
  -- Precompute b·xⁱ for i = 0,1,2,3 (the four bit positions within a nibble).
  let s0 := shiftLeftU64ToU128 b 0   -- b·x⁰
  let s1 := shiftLeftU64ToU128 b 1   -- b·x¹
  let s2 := shiftLeftU64ToU128 b 2   -- b·x²
  let s3 := shiftLeftU64ToU128 b 3   -- b·x³
  -- t_n = XOR of sᵢ for each bit i set in n. This is the product of nibble n with b.
  -- e.g. t6 = s1 ⊕ s2 because 6 = 0b0110, bits 1 and 2 are set.
  let t0  : U128 := ⟨0, 0⟩
  let t1  := s0
  let t2  := s1
  let t3  := s0 ^^^ s1
  let t4  := s2
  let t5  := s0 ^^^ s2
  let t6  := s1 ^^^ s2
  let t7  := s0 ^^^ s1 ^^^ s2
  let t8  := s3
  let t9  := s0 ^^^ s3
  let t10 := s1 ^^^ s3
  let t11 := s0 ^^^ s1 ^^^ s3
  let t12 := s2 ^^^ s3
  let t13 := s0 ^^^ s2 ^^^ s3
  let t14 := s1 ^^^ s2 ^^^ s3
  let t15 := s0 ^^^ s1 ^^^ s2 ^^^ s3
  let selectNibble (n : UInt64) : U128 :=
    match n.toNat with
    | 0  => t0  | 1  => t1  | 2  => t2  | 3  => t3
    | 4  => t4  | 5  => t5  | 6  => t6  | 7  => t7
    | 8  => t8  | 9  => t9  | 10 => t10 | 11 => t11
    | 12 => t12 | 13 => t13 | 14 => t14 | _  => t15
  -- Walk the 16 nibbles of `a` from most-significant to least-significant.
  -- For each nibble at bit-position shift = 4·n, look up the precomputed product
  -- and XOR it into the accumulator shifted to the right position.
  let rec go : Nat → U128 → U128
    | 0,       acc => acc
    | (n + 1), acc =>
      let shift : Nat := 4 * n
      let nibble : UInt64 := (a >>> UInt64.ofNat shift) &&& 0xF
      go n (acc ^^^ shiftLeftU128 (selectNibble nibble) shift)
  go 16 ⟨0, 0⟩

/-! ## Base multiply 2: C-backed 64-bit loop

`clMul64_fast_spec` is a Lean function that mirrors the C loop in `clMul64.c` exactly.
It is the proof target — we prove this spec equals `BinaryField.clMul`.

`clMul64_fast_c` is an opaque declaration bound to the C symbol `compoly_clmul64`.
Lean has no semantics for C; we cannot prove it correct inside Lean. Instead:
- `@[implemented_by clMul64_fast_c]` tells the compiler: use the C function at runtime.
- `checkClMul64` in `BenchForFastMul.lean` tests them empirically on 100,000 inputs.

This design means all proofs work against the Lean spec, while runtime performance
comes from C. -/

/-- Lean spec of the C loop in `clMul64.c`.
    Invariant: after iteration i, (lo, hi) represents ∑_{j < i} bit_j(a)·b·xʲ.
    The `i == 0` guard on `hi` avoids a right-shift by 64 (undefined behaviour in C). -/
def clMul64_fast_spec (a b : UInt64) : U128 :=
  let rec go (i : Nat) (lo hi : UInt64) : U128 :=
    if i < 64 then
      let i64 : UInt64 := UInt64.ofNat i
      -- bit = 1 if bit i of a is set, else 0. Multiplying by bit acts as a conditional.
      let bit : UInt64 := (a >>> i64) &&& 1
      -- XOR b shifted left by i into the low word (bits 0..63 of b·xⁱ).
      let lo' := lo ^^^ (bit * (b <<< i64))
      -- XOR b shifted right by (64-i) into the high word (bits 64..127 of b·xⁱ).
      -- Skipped for i=0 because b>>>64 is UB in C and zero in Lean (both mean: no hi bits).
      let hi' := if i == 0 then hi else hi ^^^ (bit * (b >>> (64 - i64)))
      go (i + 1) lo' hi'
    else
      ⟨lo, hi⟩
  go 0 0 0

/-- C function `compoly_clmul64` from `clMul64.c`, linked via `lakefile.lean`.
    Declared `opaque` so Lean cannot unfold it — it has no Lean definition. -/
@[extern "compoly_clmul64"]
opaque clMul64_fast_c (a b : UInt64) : U128

/-- Public 64-bit multiply: uses `clMul64_fast_spec` as its Lean definition (for proofs)
    but substitutes `clMul64_fast_c` at runtime via `@[implemented_by]`. -/
@[implemented_by clMul64_fast_c]
def clMul64_fast (a b : UInt64) : U128 :=
  clMul64_fast_spec a b

/-! ## Karatsuba: C-backed path

Both levels use the same identity. For 128×128:
  z0 = lo(a) · lo(b)
  z2 = hi(a) · hi(b)
  z1 = (lo(a) ⊕ hi(a)) · (lo(b) ⊕ hi(b)) ⊕ z0 ⊕ z2

The 256-bit result assembles as:
  [z0.lo | z0.hi⊕z1.lo | z1.hi⊕z2.lo | z2.hi]
          ^^^^^^^^^^^^^^^^^^^^^^^^^^^
          the middle 128 bits are where the Karatsuba cross-term sits.

The 256×256 level is identical with 128-bit halves replacing 64-bit halves.
We only keep the low 256 bits of the product (sufficient for reduction in GF(2²⁵⁶)). -/

/-- Karatsuba 128×128 carry-less multiply → 256-bit result. Base: `clMul64_fast` (C). -/
def clMul128K (a b : U128) : U256 :=
  let z0 := clMul64_fast a.lo b.lo
  let z2 := clMul64_fast a.hi b.hi
  let z1 := clMul64_fast (a.lo ^^^ a.hi) (b.lo ^^^ b.hi) ^^^ z0 ^^^ z2
  ⟨z0.lo, z0.hi ^^^ z1.lo, z1.hi ^^^ z2.lo, z2.hi⟩

/-- Karatsuba 256×256 carry-less multiply → low 256 bits of the product. Base: `clMul128K`. -/
def clMul256K (a b : U256) : U256 :=
  let z0 := clMul128K a.lo128 b.lo128
  let z2 := clMul128K a.hi128 b.hi128
  let z1 := clMul128K (a.lo128 ^^^ a.hi128) (b.lo128 ^^^ b.hi128) ^^^ z0 ^^^ z2
  -- Only the low 256 bits: words 0,1 from z0, then the Karatsuba cross-term for words 2,3.
  -- Words 4–7 (the high half of the full 512-bit product) are discarded.
  ⟨z0.w0, z0.w1, z0.w2 ^^^ z1.w0, z0.w3 ^^^ z1.w1⟩

/-! ## Karatsuba: pure Lean path

Identical structure to the C-backed path but uses `clMul64` (pure Lean 4-bit window)
as the base. Slower at runtime (~17× vs C-backed) but has no opaque functions,
making it fully amenable to Lean proofs. -/

/-- Karatsuba 128×128 carry-less multiply → 256-bit result. Base: `clMul64` (pure Lean). -/
def clMul128K_pure (a b : U128) : U256 :=
  let z0 := clMul64 a.lo b.lo
  let z2 := clMul64 a.hi b.hi
  let z1 := clMul64 (a.lo ^^^ a.hi) (b.lo ^^^ b.hi) ^^^ z0 ^^^ z2
  ⟨z0.lo, z0.hi ^^^ z1.lo, z1.hi ^^^ z2.lo, z2.hi⟩

/-- Karatsuba 256×256 carry-less multiply → low 256 bits. Base: `clMul128K_pure`. -/
def clMul256K_pure (a b : U256) : U256 :=
  let z0 := clMul128K_pure a.lo128 b.lo128
  let z2 := clMul128K_pure a.hi128 b.hi128
  let z1 := clMul128K_pure (a.lo128 ^^^ a.hi128) (b.lo128 ^^^ b.hi128) ^^^ z0 ^^^ z2
  ⟨z0.w0, z0.w1, z0.w2 ^^^ z1.w0, z0.w3 ^^^ z1.w1⟩

/-! ## Conversion between B256 and U256

`B256 = BitVec 256 = Lean Nat (GMP)`. Converting between B256 and U256 requires
slicing the 256-bit value into 64-bit chunks and back. These conversions are the
bottleneck in the full pipeline (~25× overhead vs the pure arithmetic cost). -/

/-- Split a B256 into four UInt64 limbs (least-significant first). -/
def toU256 (v : B256) : U256 :=
  ⟨UInt64.ofNat (BitVec.extractLsb 63  0   v).toNat,
   UInt64.ofNat (BitVec.extractLsb 127 64  v).toNat,
   UInt64.ofNat (BitVec.extractLsb 191 128 v).toNat,
   UInt64.ofNat (BitVec.extractLsb 255 192 v).toNat⟩

/-- Reassemble a B256 from four UInt64 limbs by shifting each limb into position and XOR-ing.
    XOR is safe here because the limbs occupy disjoint bit ranges. -/
def ofU256 (v : U256) : B256 :=
  BitVec.ofNat 256 v.w0.toNat ^^^
  (BitVec.ofNat 256 v.w1.toNat <<< 64) ^^^
  (BitVec.ofNat 256 v.w2.toNat <<< 128) ^^^
  (BitVec.ofNat 256 v.w3.toNat <<< 192)

/-! ## Partial conversion proof -/

/-- The low 64 bits of `ofU256 u` equal `w0`. Proved by bit-level reasoning.
    This is the first step toward proving the full roundtrip `ofU256 ∘ toU256 = id`. -/
lemma extractLsb_ofU256_lo (u : U256) :
    BitVec.extractLsb 63 0 (ofU256 u) = BitVec.ofNat 64 u.w0.toNat := by
  apply (BitVec.eq_of_getLsbD_eq_iff).2
  intro i hi
  have hi128 : i < 128 := Nat.lt_trans hi (by decide)
  have hi192 : i < 192 := Nat.lt_trans hi (by decide)
  have hi256 : i < 256 := Nat.lt_trans hi (by decide)
  simp [ofU256, hi, hi128, hi192, hi256]
  simp [BitVec.getElem_eq_testBit_toNat]
  calc
    (u.w0.toNat % 2^256).testBit i
        = (decide (i < 256) && u.w0.toNat.testBit i) := by
            simpa using (Nat.testBit_mod_two_pow (u.w0.toNat) 256 i)
    _ = u.w0.toNat.testBit i := by simp [hi256]

/-! ## Top-level API

The `@[implemented_by]` pattern:
- In Lean (for proofs), `clMulFast a b` *is* `BinaryField.clMul a b` by definition.
- At runtime, the compiler replaces the body with `clMulFast_impl a b` (the fast path).
- `clMulFast_eq_clMul` therefore holds by `rfl` — no proof effort required.
- The remaining obligation is proving `clMulFast_impl` correct (see lemmas below). -/

/-- Runtime implementation: convert to U256, run C-backed Karatsuba, convert back. -/
def clMulFast_impl (a b : B256) : B256 :=
  ofU256 (clMul256K (toU256 a) (toU256 b))

/-- Runtime implementation: same pipeline using pure Lean Karatsuba. -/
def clMulFast_pure_impl (a b : B256) : B256 :=
  ofU256 (clMul256K_pure (toU256 a) (toU256 b))

/-- Fast carry-less multiplication (C-backed Karatsuba). Defined as `clMul` for proofs;
    `clMulFast_impl` runs at runtime. -/
@[implemented_by clMulFast_impl]
def clMulFast (a b : B256) : B256 :=
  BinaryField.clMul a b

/-- Pure Lean carry-less multiplication (4-bit window Karatsuba). Defined as `clMul` for
    proofs; `clMulFast_pure_impl` runs at runtime. -/
@[implemented_by clMulFast_pure_impl]
def clMulFast_pure (a b : B256) : B256 :=
  BinaryField.clMul a b

/-- Fast carry-less squaring: square by multiplying a value by itself (C-backed). -/
def clSqFast (a : B128) : B256 :=
  clMulFast (BinaryField.to256 a) (BinaryField.to256 a)

/-- Pure Lean carry-less squaring. -/
def clSqFast_pure (a : B128) : B256 :=
  clMulFast_pure (BinaryField.to256 a) (BinaryField.to256 a)

/-! ## Top-level correctness theorems (trivially true by definition) -/

theorem clMulFast_eq_clMul (a b : B256) : clMulFast a b = BinaryField.clMul a b := rfl
theorem clMulFast_pure_eq_clMul (a b : B256) : clMulFast_pure a b = BinaryField.clMul a b := rfl
theorem clSqFast_eq_clSq (a : B128) : clSqFast a = BinaryField.clSq a := rfl
theorem clSqFast_pure_eq_clSq (a : B128) : clSqFast_pure a = BinaryField.clSq a := rfl

/-! ## Embedding helper for proof statements -/

/-- Embed a U128 product into B256 with the upper 128 bits zeroed.
    Used to state correctness theorems for the 64-bit base cases. -/
def U128.toB256 (r : U128) : B256 :=
  BitVec.ofNat 256 r.lo.toNat ^^^ (BitVec.ofNat 256 r.hi.toNat <<< 64)

/-! ## Intermediate correctness lemmas

These are the open proof obligations. Together they form a complete proof chain:

  clMul64_fast_spec_correct          (base case: bit-loop spec = clMul on 64-bit inputs)
    ↓ (Karatsuba identity at 128-bit level)
  clMul128K_correct                  (C-backed 128×128 = clMul on U128 inputs)
    ↓ (same identity at 256-bit level)
  clMul256K_correct                  (C-backed 256×256 = clMul on U256 inputs)
    ↓ + ofU256_toU256
  clMulFast_impl_correct             (full pipeline = clMul on B256 inputs)

An analogous chain exists for the pure Lean path via clMul64_correct.
Once these are proved, `clMulFast_eq_clMul` is already `rfl` — nothing more is needed
for the public API. -/

/-- Roundtrip B256 → U256 → B256. Proof: BitVec extract/reassemble are inverses.
    Should follow from `omega` or `decide` via `extractLsb_ofU256_lo` and analogues. -/
theorem ofU256_toU256 (a : B256) : ofU256 (toU256 a) = a := by sorry

/-- Roundtrip U256 → B256 → U256. Proof: extractLsb of each limb recovers the original word. -/
theorem toU256_ofU256 (u : U256) : toU256 (ofU256 u) = u := by sorry

/-- The 4-bit window correctly computes 64-bit carry-less multiplication.
    Proof sketch: induction showing the nibble accumulation equals ∑_{i<64} bit_i(a)·b·xⁱ. -/
theorem clMul64_correct (a b : UInt64) :
    (clMul64 a b).toB256 =
    BinaryField.clMul (BitVec.ofNat 256 a.toNat) (BitVec.ofNat 256 b.toNat) := by sorry

/-- The bit-loop spec correctly computes 64-bit carry-less multiplication.
    Proof sketch: induction on `go` with invariant
    `(lo, hi) = ∑_{j<i} bit_j(a)·b·xʲ` as a polynomial over GF(2). -/
theorem clMul64_fast_spec_correct (a b : UInt64) :
    (clMul64_fast_spec a b).toB256 =
    BinaryField.clMul (BitVec.ofNat 256 a.toNat) (BitVec.ofNat 256 b.toNat) := by sorry

/-- C-backed Karatsuba 128×128 is correct.
    Follows from `clMul64_fast_spec_correct` and the Karatsuba identity. -/
theorem clMul128K_correct (a b : U128) :
    ofU256 (clMul128K a b) = BinaryField.clMul a.toB256 b.toB256 := by sorry

/-- C-backed Karatsuba 256×256 is correct (low 256 bits).
    Follows from `clMul128K_correct` and the same Karatsuba identity one level up. -/
theorem clMul256K_correct (a b : U256) :
    ofU256 (clMul256K a b) = BinaryField.clMul (ofU256 a) (ofU256 b) := by sorry

/-- The full C-backed pipeline is correct.
    Proof: `clMul256K_correct` + `ofU256_toU256`. -/
theorem clMulFast_impl_correct (a b : B256) :
    clMulFast_impl a b = BinaryField.clMul a b := by
  unfold clMulFast_impl
  rw [clMul256K_correct, ofU256_toU256, ofU256_toU256]

/-- Pure Lean Karatsuba 128×128 is correct. Follows from `clMul64_correct`. -/
theorem clMul128K_pure_correct (a b : U128) :
    ofU256 (clMul128K_pure a b) = BinaryField.clMul a.toB256 b.toB256 := by sorry

/-- Pure Lean Karatsuba 256×256 is correct. Follows from `clMul128K_pure_correct`. -/
theorem clMul256K_pure_correct (a b : U256) :
    ofU256 (clMul256K_pure a b) = BinaryField.clMul (ofU256 a) (ofU256 b) := by sorry

/-- The full pure Lean pipeline is correct. Follows from `clMul256K_pure_correct` + `ofU256_toU256`. -/
theorem clMulFast_pure_impl_correct (a b : B256) :
    clMulFast_pure_impl a b = BinaryField.clMul a b := by
  unfold clMulFast_pure_impl
  rw [clMul256K_pure_correct, ofU256_toU256, ofU256_toU256]

end clMulFast
end BinaryField
