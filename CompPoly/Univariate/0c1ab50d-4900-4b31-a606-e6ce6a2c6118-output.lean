/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0c1ab50d-4900-4b31-a606-e6ce6a2c6118

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma smul_mulPowX_coeff (a : R) (q : CPolynomial R) (i k : ℕ) :
    ((smul a q).mulPowX i).coeff k = if k < i then 0 else a * q.coeff (k - i)

- lemma mul_coeff_list (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (p.zipIdx.toList.map
      (fun ⟨a, i⟩ => if k < i then 0 else a * q.coeff (k - i))).sum

- lemma sum_zipIdx_eq_sum_range {α : Type*} [AddCommMonoid α] (p : CPolynomial R) (f : R → ℕ → α) :
    (p.zipIdx.toList.map (fun ⟨a, i⟩ => f a i)).sum =
    (Finset.range p.size).sum (fun i => f (p.coeff i) i)

- lemma mul_coeff_range_size (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (Finset.range p.size).sum
      (fun i => if k < i then 0 else p.coeff i * q.coeff (k - i))

- lemma sum_range_extend (p q : CPolynomial R) (k : ℕ) :
    (Finset.range p.size).sum (fun i => if k < i then 0 else p.coeff i * q.coeff (k - i)) =
    (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i))

- theorem mul_mul_coeff (p q r : CPolynomial R) (n : ℕ) :
    ((p * q) * r).coeff n =
      (Finset.range (n + 1)).sum (fun j =>
        (Finset.range (j + 1)).sum (fun i =>
          p.coeff i * q.coeff (j - i) * r.coeff (n - j)))

- theorem double_sum_eq (p q r : CPolynomial R) (n : ℕ) :
    (Finset.range (n + 1)).sum (fun j =>
      (Finset.range (j + 1)).sum (fun i =>
        p.coeff i * q.coeff (j - i) * r.coeff (n - j)))
    =
    (Finset.range (n + 1)).sum (fun i =>
      (Finset.range (n - i + 1)).sum (fun k =>
        p.coeff i * q.coeff k * r.coeff (n - i - k)))
-/

/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import CompPoly.Univariate.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


/-!
# Associativity of CPolynomial Multiplication

This file contains a proof of the associativity of `CPolynomial.mul`.

## Strategy

The multiplication `p * q` is defined as `Σᵢ (aᵢ • q) * X^i` where `p = Σᵢ aᵢXⁱ`.

To prove `(p * q) * r = p * (q * r)`, we show that both sides have equal coefficients.
The key identity is that `coeff ((p * q) * r) n = Σᵢⱼₖ pᵢ * qⱼ * rₖ` (summed over i+j+k=n),
which equals `coeff (p * (q * r)) n` by associativity in R.

## Main Results

- `mul_coeff`: The coefficient of `(p * q)` at index `k` is `Σᵢ pᵢ * q_{k-i}`
- `mul_assoc_coeff`: Coefficients of `(p * q) * r` and `p * (q * r)` agree
- `mul_assoc'`: Associativity of multiplication
-/

namespace CompPoly.CPolynomial

open CompPoly.CPolynomial

open Finset BigOperators

variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]

/-! ### Helper lemmas for coefficients -/

/-- Helper: coefficient of smul -/
lemma smul_coeff (a : R) (p : CPolynomial R) (k : ℕ) :
    (smul a p).coeff k = a * p.coeff k := by
  exact smul_equiv p k a

/-- Helper: coefficient of mulPowX -/
lemma mulPowX_coeff' (p : CPolynomial R) (n k : ℕ) :
    (p.mulPowX n).coeff k = if k < n then 0 else p.coeff (k - n) := by
  exact coeff_mulPowX p n k

/-- Combining smul and mulPowX for the multiplication formula -/
lemma smul_mulPowX_coeff (a : R) (q : CPolynomial R) (i k : ℕ) :
    ((smul a q).mulPowX i).coeff k = if k < i then 0 else a * q.coeff (k - i) := by
    convert mulPowX_coeff' (CompPoly.CPolynomial.smul a q) i k using 1;
    rw [ smul_coeff ]

/-
  rw [mulPowX_coeff', smul_coeff]
  split_ifs <;> ring
  -/

/-- The empty polynomial has coefficient 0 everywhere -/
lemma empty_coeff (k : ℕ) : (mk #[] : CPolynomial R).coeff k = 0 := by
  simp [coeff, mk]

/-! ### Coefficient of multiplication -/

/-- Express mul as a foldl that adds terms -/
lemma mul_eq_foldl (p q : CPolynomial R) :
    p * q = p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + (smul a q).mulPowX i) (mk #[]) := by
  rfl

/-- The coefficient of `p * q` at index `k`, expressed as a sum over indices of p.
    This is an intermediate form before converting to Finset.range. -/
lemma mul_coeff_list (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (p.zipIdx.toList.map
      (fun ⟨a, i⟩ => if k < i then 0 else a * q.coeff (k - i))).sum := by
        convert coeff_foldl_add _ _ _ _ using 1;
        case convert_4 => exact R × ℕ;
        convert rfl;
        rotate_left;
        rotate_left;
        (expose_names; exact inst_1)
        (expose_names; exact inst_2)
        exact ( Array.zipIdx p ).toList;
        exact fun x => ( smul x.1 q ).mulPowX x.2;
        exact mk #[];
        · convert mul_eq_foldl p q |> Eq.symm;
          grind;
        · -- By definition of `mulPowX`, we know that `(mulPowX x.2 (smul x.1 q)).coeff k` is equal to `if k < x.2 then 0 else x.1 * q.coeff (k - x.2)`.
          have h_mulPowX_coeff : ∀ x : R × ℕ, (mulPowX x.2 (smul x.1 q)).coeff k = if k < x.2 then 0 else x.1 * q.coeff (k - x.2) := by
             exact fun x => smul_mulPowX_coeff x.1 q x.2 k
          aesop

/-
  rw [mul_eq_foldl]
  have h := coeff_foldl_add (p.zipIdx.toList) (fun ⟨a, i⟩ => (smul a q).mulPowX i) (mk #[]) k
  simp only [Array.foldl_toList] at h
  rw [h, empty_coeff, zero_add]
  congr 1
  apply List.map_congr_left
  intro ⟨a, i⟩ _
  exact smul_mulPowX_coeff a q i k
  -/

/-- Sum over list zipIdx equals sum over Finset.range for the relevant terms -/
lemma sum_zipIdx_eq_sum_range {α : Type*} [AddCommMonoid α] (p : CPolynomial R) (f : R → ℕ → α) :
    (p.zipIdx.toList.map (fun ⟨a, i⟩ => f a i)).sum =
    (Finset.range p.size).sum (fun i => f (p.coeff i) i) := by
      refine' congr_arg _ ( List.ext_get _ _ ) <;> aesop

/-
  induction p using Array.recOn with
  | empty => simp
  | append a as ih =>
    simp only [Array.zipIdx_append, Array.toList_append, List.map_append, List.sum_append]
    rw [ih]
    simp only [Array.size_append, Array.size_singleton]
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      congr 1
      · simp [coeff, hi]
    · simp only [Array.zipIdx_singleton, Array.toList_singleton, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      congr 1
      simp [coeff]-/

/-- The coefficient of `p * q` at index `k`, as a sum over 0..p.size-1 -/
lemma mul_coeff_range_size (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (Finset.range p.size).sum
      (fun i => if k < i then 0 else p.coeff i * q.coeff (k - i)) := by
        have h_coeff_mul_ci : (p * q).coeff k = (p.zipIdx.toList.map (fun ⟨a, i⟩ => if k < i then 0 else a * q.coeff (k - i))).sum := by
          exact mul_coeff_list p q k
        convert sum_zipIdx_eq_sum_range p ( fun a i => if k < i then 0 else a * q.coeff ( k - i ) ) using 1

/-
  rw [mul_coeff_list]
  rw [sum_zipIdx_eq_sum_range]-/

/-- Extend a sum from range p.size to range (k+1) by noting extra terms are 0 -/
lemma sum_range_extend (p q : CPolynomial R) (k : ℕ) :
    (Finset.range p.size).sum (fun i => if k < i then 0 else p.coeff i * q.coeff (k - i)) =
    (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i)) := by
      by_cases h : p.size ≤ k + 1;
      · rw [ ← Finset.sum_range_add_sum_Ico _ h ];
        rw [ Finset.sum_congr rfl fun i hi => if_neg ( by linarith [ Finset.mem_range.mp hi ] ), Finset.sum_Ico_eq_sum_range ];
        simp +decide [ CompPoly.CPolynomial.coeff ];
      · rw [ Finset.sum_ite ];
        rw [ show Finset.filter ( fun x => ¬k < x ) ( Finset.range ( Array.size p ) ) = Finset.range ( k + 1 ) from ?_ ];
        · simp +zetaDelta at *;
        · grind

/-
  -- Split the sum based on whether i < p.size or not, and whether i ≤ k or not
  by_cases h : p.size ≤ k + 1
  · -- p.size ≤ k + 1: extend the range
    rw [← Finset.sum_range_add_sum_Ico _ h]
    simp only [add_right_eq_self]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_Ico] at hi
    -- i ≥ p.size, so p.coeff i = 0
    simp [coeff, hi.1]
  · -- p.size > k + 1: truncate the range
    push_neg at h
    have hk : k + 1 ≤ p.size := Nat.le_of_lt h
    rw [← Finset.sum_range_add_sum_Ico _ hk]
    simp only [self_eq_add_right]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_Ico] at hi
    -- i > k, so the if gives 0
    simp [hi.1]-/

/-- The coefficient of `p * q` at index `k` is the convolution sum `Σᵢ pᵢ * q_{k-i}`. -/
theorem mul_coeff (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (Finset.range (k + 1)).sum (fun i => p.coeff i * q.coeff (k - i)) := by
  rw [mul_coeff_range_size, sum_range_extend]

/-! ### Triple product coefficients -/

/-- The coefficient of `(p * q) * r` at index `n`. -/
theorem mul_mul_coeff (p q r : CPolynomial R) (n : ℕ) :
    ((p * q) * r).coeff n =
      (Finset.range (n + 1)).sum (fun j =>
        (Finset.range (j + 1)).sum (fun i =>
          p.coeff i * q.coeff (j - i) * r.coeff (n - j))) := by
            convert mul_coeff _ _ _;
            · rw [ mul_coeff, Finset.sum_mul _ _ _ ];
            · (expose_names; exact inst_2)

/-
  rw [mul_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_coeff]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring-/

/-- The coefficient of `p * (q * r)` at index `n`. -/
theorem mul_assoc_coeff_rhs (p q r : CPolynomial R) (n : ℕ) :
    (p * (q * r)).coeff n =
      (Finset.range (n + 1)).sum (fun i =>
        (Finset.range (n - i + 1)).sum (fun j =>
          p.coeff i * q.coeff j * r.coeff (n - i - j))) := by
  rw [mul_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_coeff]
  simp only [Finset.mem_range] at hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  grind

/-! ### The key combinatorial identity -/

/-- The set of pairs (i, j) with i ≤ j ≤ n -/
def triangleSet (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1)).biUnion (fun j => (Finset.range (j + 1)).map ⟨fun i => (i, j), fun _ _ h => by simp at h; exact h⟩)

/-- The set of pairs (i, k) with i + k ≤ n -/
def triangleSet' (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1)).biUnion (fun i => (Finset.range (n - i + 1)).map ⟨fun k => (i, k), fun _ _ h => by simp at h; exact h⟩)

/-- Key lemma: The double sums are equal via a change of variables.

In the LHS, we sum over (i, j) with 0 ≤ i ≤ j ≤ n, computing p_i * q_{j-i} * r_{n-j}.
In the RHS, we sum over (i, k) with i + k ≤ n, computing p_i * q_k * r_{n-i-k}.

Setting k = j - i (so j = i + k), these are the same sum.
-/
theorem double_sum_eq (p q r : CPolynomial R) (n : ℕ) :
    (Finset.range (n + 1)).sum (fun j =>
      (Finset.range (j + 1)).sum (fun i =>
        p.coeff i * q.coeff (j - i) * r.coeff (n - j)))
    =
    (Finset.range (n + 1)).sum (fun i =>
      (Finset.range (n - i + 1)).sum (fun k =>
        p.coeff i * q.coeff k * r.coeff (n - i - k))) := by
          -- By interchanging the order of summation, we can rewrite the double sum.
          have h_interchange : ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (j + 1), p.coeff i * q.coeff (j - i) * r.coeff (n - j) = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.Ico i (n + 1), p.coeff i * q.coeff (j - i) * r.coeff (n - j) := by
            rw [ Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm ];
          convert h_interchange using 2;
          rw [ Finset.sum_Ico_eq_sum_range ];
          simp +decide [ Nat.sub_add_comm ( Finset.mem_range_succ_iff.mp ‹_› ) ];
          exact Finset.sum_congr rfl fun _ _ => by rw [ Nat.sub_sub ] ;

/-
  -- Both sides sum the same terms, just indexed differently
  -- LHS: sum over j from 0 to n, then i from 0 to j
  --      term is p_i * q_{j-i} * r_{n-j}
  -- RHS: sum over i from 0 to n, then k from 0 to n-i
  --      term is p_i * q_k * r_{n-i-k}
  -- With k = j - i, we have j = i + k, and the terms match

  -- Use Finset.sum_comm to swap the order of summation, then reindex
  -- First, express LHS as sum over the triangle {(i,j) : i ≤ j ≤ n}
  -- Then reindex with k = j - i

  -- Direct approach: convert both to sums over the same index set
  trans (Finset.range (n + 1)).sum (fun i =>
    (Finset.range (n + 1)).sum (fun j =>
      if i ≤ j then p.coeff i * q.coeff (j - i) * r.coeff (n - j) else 0))
  · -- LHS = sum with indicator
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with h
    · rfl
    · push_neg at h
      -- i > j means i is not in range (j+1)
      have : i ∉ Finset.range (j + 1) := by simp; omega
      simp [Finset.sum_eq_zero_iff]
      sorry -- need to handle this case
  · -- Sum with indicator = RHS
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    -- Change variable: k = j - i, so j = i + k
    -- When j ranges from i to n, k ranges from 0 to n - i
    trans (Finset.range (n - i + 1)).sum (fun k =>
      p.coeff i * q.coeff k * r.coeff (n - i - k))
    · -- Reindex: j ↦ k = j - i
      rw [← Finset.sum_map (Finset.range (n - i + 1)) ⟨fun k => i + k, fun _ _ h => by omega⟩]
      apply Finset.sum_congr
      · ext j
        simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨k, hk, rfl⟩
          constructor
          · omega
          · split_ifs with h
            · rfl
            · omega
        · intro ⟨hj, hij⟩
          split_ifs at hij with h
          · use j - i
            constructor
            · omega
            · omega
          · push_neg at h
            omega
      · intro j hj
        simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hj
        obtain ⟨k, hk, rfl⟩ := hj
        simp only [add_tsub_cancel_left, ite_true]
        congr 1
        omega
    · rfl
      -/

/-! ### Main associativity theorem -/

/-- Coefficients of `(p * q) * r` and `p * (q * r)` are equal. -/
theorem mul_assoc_coeff (p q r : CPolynomial R) (n : ℕ) :
    ((p * q) * r).coeff n = (p * (q * r)).coeff n := by
  rw [mul_mul_coeff, mul_assoc_coeff_rhs, double_sum_eq]

/-- The two products are equivalent (have equal coefficients everywhere). -/
theorem mul_assoc_equiv (p q r : CPolynomial R) :
    Trim.equiv ((p * q) * r) (p * (q * r)) := by
  intro i
  exact mul_assoc_coeff p q r i

/-- Associativity of CPolynomial multiplication. -/
theorem mul_assoc' (p q r : CPolynomial R) : (p * q) * r = p * (q * r) := by
  -- Both sides are already trimmed (by mul_is_trimmed)
  -- So we can use canonical_ext
  apply Trim.canonical_ext
  · exact mul_is_trimmed (p * q) r
  · exact mul_is_trimmed p (q * r)
  · exact mul_assoc_equiv p q r

end CompPoly.CPolynomial
