/-
Proof outline for mul_comm in CPolynomial

The goal is to prove: p * q = q * p for [CommRing R] [LawfulBEq R]

Strategy: Follow the same pattern as mul_assoc
1. Show coefficients are equal using the convolution formula
2. Use Trim.canonical_ext since both sides are already trimmed
-/

import CompPoly.Univariate.Basic

namespace CompPoly.CPolynomial

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]

/-
## Key Insight

From `mul_coeff` we have:
  (p * q).coeff k = (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i))
  (q * p).coeff k = (Finset.range (k + 1)).sum (fun i => q.coeff i * p.coeff (k - i))

We need to show these sums are equal. The key steps:

1. In CommRing R, we have `a * b = b * a`
2. The sum `Σᵢ p.coeff i * q.coeff (k - i)` over i ∈ [0, k]
   equals `Σⱼ p.coeff (k - j) * q.coeff j` by substitution j = k - i
3. Using commutativity: `p.coeff (k - j) * q.coeff j = q.coeff j * p.coeff (k - j)`
4. This is exactly the sum for `(q * p).coeff k`
-/

/-- The convolution sum is symmetric under reversal of the range. -/
lemma sum_range_reverse (p q : CPolynomial R) (k : ℕ) :
    (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i)) =
    (Finset.range (k + 1)).sum (fun j => p.coeff (k - j) * q.coeff j) := by
  -- sum_range_reflect: Σ_{j < n} f(n-1-j) = Σ_{j < n} f(j)
  -- For n = k+1: Σ_{j < k+1} f(k-j) = Σ_{j < k+1} f(j)
  -- We want to show: Σ p[i]*q[k-i] = Σ p[k-j]*q[j]
  -- The RHS has the "reflected" form, so apply reflect to get LHS form
  rw [← Finset.sum_range_reflect (fun j => p.coeff (k - j) * q.coeff j) (k + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  -- j < k + 1 means j ≤ k
  have hj' : j ≤ k := Nat.lt_succ_iff.mp hj
  -- Goal: p.coeff (k - (k - j)) * q.coeff (k - j) = p.coeff j * q.coeff (k - j)
  -- Use Nat.sub_sub_self: k - (k - j) = j when j ≤ k
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hj']

/-- Using commutativity of R to swap the multiplication order. -/
lemma mul_coeff_comm (p q : CPolynomial R) (k : ℕ) :
    (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i)) =
    (Finset.range (k + 1)).sum (fun i => q.coeff i * p.coeff (k - i)) := by
  -- Step 1: Reverse the sum (substitute j = k - i)
  rw [sum_range_reverse]
  -- Step 2: Use commutativity in R
  apply Finset.sum_congr rfl
  intro j _
  ring  -- or: rw [mul_comm]

/-- Coefficients of p * q and q * p are equal. -/
theorem mul_comm_coeff (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (q * p).coeff k := by
  rw [mul_coeff, mul_coeff]
  exact mul_coeff_comm p q k

/-- p * q and q * p are equivalent (have equal coefficients everywhere). -/
theorem mul_comm_equiv (p q : CPolynomial R) :
    Trim.equiv (p * q) (q * p) := by
  intro i
  exact mul_comm_coeff p q i

/-- Commutativity of multiplication for CPolynomial over a CommRing. -/
theorem mul_comm' (p q : CPolynomial R) : p * q = q * p := by
  apply Trim.canonical_ext
  · exact mul_is_trimmed p q
  · exact mul_is_trimmed q p
  · exact mul_comm_equiv p q

end CompPoly.CPolynomial

/-
## Summary of proof structure

The proof follows these lemmas in order:

1. `sum_range_reverse`: Shows Σᵢ f(i) = Σⱼ f(k-j) over [0,k]
   - Uses `Finset.sum_range_reflect`
   - This is a pure index substitution, works in any ring

2. `mul_coeff_comm`: Shows the convolution sums are equal
   - Combines sum reversal with commutativity of R
   - `p[i] * q[k-i]` summed = `q[i] * p[k-i]` summed

3. `mul_comm_coeff`: Each coefficient is equal
   - Direct application of `mul_coeff` and `mul_coeff_comm`

4. `mul_comm_equiv`: The polynomials are equivalent
   - Wraps `mul_comm_coeff` in `Trim.equiv`

5. `mul_comm'`: Final equality
   - Uses `Trim.canonical_ext` since both products are already trimmed
   - This is the same pattern as `mul_assoc`

## Key lemmas from Basic.lean used:

- `mul_coeff` (line 1188): (p * q).coeff k = Σᵢ p.coeff i * q.coeff (k - i)
- `mul_is_trimmed` (line 832): (p * q).trim = p * q
- `Trim.canonical_ext` (line 403): canonical polys with equiv coeffs are equal
- `Trim.equiv` (line 257): equivalence = all coefficients equal

## Potential issues to watch for:

1. `Finset.sum_range_reflect` might need the right form. Check the exact signature:
   It should give: Σ_{i<n} f(i) = Σ_{i<n} f(n-1-i) or similar
   You may need to adjust indices by ±1

2. The `omega` tactic should handle the index arithmetic but if not, you may need
   explicit `Nat.sub_sub_self` or similar lemmas

3. If `ring` doesn't work for the commutativity step, use explicit `mul_comm`
-/
