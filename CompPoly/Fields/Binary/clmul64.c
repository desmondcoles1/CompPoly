// clMul64.c — C backend for 64-bit carry-less multiplication
//
// WHAT THIS DOES
// ==============
// Carry-less multiplication (also called XOR multiplication or polynomial
// multiplication over GF(2)) multiplies two polynomials whose coefficients
// are bits, where addition is XOR and there is no carry between positions.
//
// Example with 4-bit inputs:
//   a = 0b1011 = x³ + x + 1
//   b = 0b0110 = x² + x
//   a·b = x⁵ + x⁴ + x³ + x⁴ + x³ + x² + x³ + x² + x
//       = x⁵ + x³ + x          (pairs cancel via XOR)
//       = 0b100010
//
// ALGORITHM
// =========
// For each bit i of `a` (0 to 63):
//   if bit i is set, XOR `b` shifted left by i into the 128-bit accumulator.
//
// The 64-bit × 64-bit product can be up to 127 bits wide, so the result is
// split across two 64-bit words:
//   lo = bits 0..63   (b << i contributes here for all i, since b<<i stays in 64 bits)
//   hi = bits 64..127 (b >> (64-i) contributes here when i > 0)
//
// The `i != 0` guard on the hi update is critical: C does not define the
// behaviour of `x >> 64` for a 64-bit type (it is undefined behaviour).
// For i=0, `b >> 64` would be UB; and the contribution to hi is zero anyway
// (b<<0 = b fits entirely in lo), so we simply skip the hi update.
//
// HOW IT CONNECTS TO LEAN
// =======================
// In clMulFast.lean, `clMul64_fast_spec` is a Lean function that mirrors this
// loop exactly. `clMul64_fast_c` is declared `opaque` with
// `@[extern "compoly_clmul64"]`, binding it to the symbol below.
// `clMul64_fast` uses `@[implemented_by clMul64_fast_c]` so proofs work against
// the Lean spec while the C loop runs at runtime.
//
// Correctness of this C function relative to the Lean spec cannot be formally
// proved inside Lean (Lean has no semantics for C). It is verified empirically
// by `BenchForFastMul.checkClMul64`, which compares both on 100,000 input pairs.
//
// LEAN OBJECT LAYOUT
// ==================
// The Lean type `U128` is `structure U128 where lo : UInt64; hi : UInt64`.
// Lean stores this as a constructor object (tag=0) with no pointer fields and
// two unboxed UInt64 scalars in the payload:
//   lean_alloc_ctor(0, 0, sizeof(uint64_t) * 2)
//     arg 0: constructor tag = 0 (first and only constructor of U128)
//     arg 1: number of pointer fields = 0 (both fields are unboxed scalars)
//     arg 2: scalar payload size in bytes = 16 (two UInt64s)
// The scalars sit at byte offsets 0 (lo) and 8 (hi) within the payload.
//   lean_ctor_set_uint64(r, 0, lo)  — writes lo at byte offset 0
//   lean_ctor_set_uint64(r, 8, hi)  — writes hi at byte offset 8

#include <lean/lean.h>
#include <stdint.h>

// LEAN_EXPORT marks the symbol as visible to Lean's runtime linker.
// The name must match the string in @[extern "compoly_clmul64"].
LEAN_EXPORT lean_obj_res compoly_clmul64(uint64_t a, uint64_t b) {
  uint64_t lo = 0;
  uint64_t hi = 0;

  for (uint32_t i = 0; i < 64; i++) {
    if ((a >> i) & 1ULL) {
      // Bit i of a is set: XOR b·xⁱ into the 128-bit accumulator.
      lo ^= b << i;
      if (i != 0) {
        // The high bits of b·xⁱ that overflow into bits 64..127.
        // Guard against i=0 to avoid b>>64 (undefined behaviour in C).
        hi ^= b >> (64 - i);
      }
    }
  }

  // Allocate a Lean U128 object and store lo and hi into its scalar payload.
  lean_object *r = lean_alloc_ctor(0, 0, sizeof(uint64_t) * 2);
  lean_ctor_set_uint64(r, 0, lo);   // lo at byte offset 0
  lean_ctor_set_uint64(r, 8, hi);   // hi at byte offset 8
  return r;
}
