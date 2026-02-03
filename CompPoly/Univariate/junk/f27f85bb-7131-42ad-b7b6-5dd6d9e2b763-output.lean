/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f27f85bb-7131-42ad-b7b6-5dd6d9e2b763

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- theorem mul_comm [CommRing R] [LawfulBEq R] (p q : CPolynomial R) : p * q = q * p

- theorem mul_distrib [LawfulBEq R] (p q r : CPolynomial R) : p * (q +r) = p * q + p * r

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```



At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

/-!
  # Computable Univariate Polynomials

  This file contains a computable datatype for univariate polynomial, `CPolynomial R`. This is
  internally represented as an array of coefficients.

  Note: this has been ported from ArkLib
-/

open Polynomial

namespace CompPoly

/-- A type analogous to `Polynomial` that supports computable operations. This is defined to be a
  wrapper around `Array`.

For example, the Array `#[1,2,3]` represents the polynomial `1 + 2x + 3x^2`.
Two arrays may represent the same polynomial via zero-padding,
for example `#[1,2,3] = #[1,2,3,0,0,0,...]`.
-/
@[reducible, inline, specialize]
def CPolynomial (R : Type*) := Array R

namespace CPolynomial

/-- Construct a `CPolynomial` from an array of coefficients. -/
@[reducible]
def mk {R : Type*} (coeffs : Array R) : CPolynomial R := coeffs

/-- Extract the underlying array of coefficients. -/
@[reducible]
def coeffs {R : Type*} (p : CPolynomial R) : Array R := p

variable {R : Type*} [Ring R] [BEq R]

variable {Q : Type*} [Ring Q]

/-- The coefficient of `X^i` in the polynomial. Returns `0` if `i` is out of bounds. -/
@[reducible]
def coeff (p : CPolynomial Q) (i : ℕ) : Q := p.getD i 0

/-- The constant polynomial `C r`. -/
def C (r : R) : CPolynomial R := #[r]

/-- The variable `X`. -/
def X : CPolynomial R := #[0, 1]

/-- Construct a monomial `c * X^n` as a `CPolynomial R`.

  The result is an array with `n` zeros followed by `c`.
  For example, `monomial 2 3` = `#[0, 0, 3]` represents `3 * X^2`.

  Note: If `c = 0`, this returns `#[]` (the zero polynomial).
-/
def monomial [DecidableEq R] (n : ℕ) (c : R) : CPolynomial R :=
  if c = 0 then #[] else .mk (Array.replicate n 0 ++ #[c])

-- TODO: Prove basic properties of `monomial`, e.g.
-- TODO: `coeff (monomial n c) i = if i = n then c else 0`
-- TODO: `monomial n 0 = 0`
-- TODO: `monomial 0 c = C c`
-- TODO: `monomial n 1 = X^n` (where `X^n` is `X.pow n`)
-- TODO: `monomial n c = C c * X^n` (multiplicative property)
-- TODO: `monomial n c + monomial n d = monomial n (c + d)` (additive property)
-- TODO: `monomial m c * monomial n d = monomial (m + n) (c * d)` (multiplicative property)
-- TODO: `trim (monomial n c) = if c = 0 then #[] else monomial n c` (canonical property)

/-- Return the index of the last non-zero coefficient of a `CPolynomial` -/
def lastNonzero (p : CPolynomial R) : Option (Fin p.size) :=
  p.findIdxRev? (· != 0)

/-- Remove leading zeroes from a `CPolynomial`.
Requires `BEq` to check if the coefficients are zero. -/
def trim (p : CPolynomial R) : CPolynomial R :=
  match p.lastNonzero with
  | none => #[]
  | some i => p.extract 0 (i.val + 1)

/-- Return the degree of a `CPolynomial`. -/
def degree (p : CPolynomial R) : Nat :=
  match p.lastNonzero with
  | none => 0
  | some i => i.val + 1

-- Aristotle skipped at least one sorry in the block below (common reasons: Aristotle does not define data).
/-- Natural number degree of a `CPolynomial`.

  Returns the degree as a natural number. For the zero polynomial, returns `0`.
  This matches Mathlib's `Polynomial.natDegree` API.
-/
def natDegree (p : CPolynomial R) : ℕ :=
  by sorry

/-- Return the leading coefficient of a `CPolynomial` as the last coefficient of the trimmed array,
or `0` if the trimmed array is empty. -/
def leadingCoeff (p : CPolynomial R) : R := p.trim.getLastD 0

namespace Trim

/-- If all coefficients are zero, `lastNonzero` is `none`. -/
theorem lastNonzero_none [LawfulBEq R] {p : CPolynomial R} :
    (∀ i, (hi : i < p.size) → p[i] = 0) → p.lastNonzero = none := by
  intro h
  apply Array.findIdxRev?_eq_none
  intros
  rw [bne_iff_ne, ne_eq, not_not]
  apply_assumption

/-- If there is a non-zero coefficient, `lastNonzero` is `some`. -/
theorem lastNonzero_some [LawfulBEq R] {p : CPolynomial R} {i} (hi : i < p.size) (h : p[i] ≠ 0) :
    ∃ k, p.lastNonzero = some k := Array.findIdxRev?_eq_some ⟨i, hi, bne_iff_ne.mpr h⟩

/-- `lastNonzero` returns the largest index with a non-zero coefficient. -/
theorem lastNonzero_spec [LawfulBEq R] {p : CPolynomial R} {k} :
    p.lastNonzero = some k
  → p[k] ≠ 0 ∧ (∀ j, (hj : j < p.size) → j > k → p[j] = 0) := by
  intro (h : p.lastNonzero = some k)
  constructor
  · by_contra
    have h : p[k] != 0 := Array.findIdxRev?_def h
    rwa [‹p[k] = 0›, bne_self_eq_false, Bool.false_eq_true] at h
  · intro j hj j_gt_k
    have h : ¬(p[j] != 0) := Array.findIdxRev?_maximal h ⟨ j, hj ⟩ j_gt_k
    rwa [bne_iff_ne, ne_eq, not_not] at h

/-- The property that an index is the last non-zero coefficient. -/
def lastNonzeroProp {p : CPolynomial R} (k : Fin p.size) : Prop :=
  p[k] ≠ 0 ∧ (∀ j, (hj : j < p.size) → j > k → p[j] = 0)

/-- The last non-zero index is unique. -/
lemma lastNonzero_unique {p : CPolynomial Q} {k k' : Fin p.size} :
    lastNonzeroProp k → lastNonzeroProp k' → k = k' := by
  suffices weaker : ∀ k k', lastNonzeroProp k → lastNonzeroProp k' → k ≤ k' by
    intro h h'
    exact Fin.le_antisymm (weaker k k' h h') (weaker k' k h' h)
  intro k k' ⟨ h_nonzero, h ⟩ ⟨ h_nonzero', h' ⟩
  by_contra k_not_le
  have : p[k] = 0 := h' k k.is_lt (Nat.lt_of_not_ge k_not_le)
  contradiction

/-- Characterization of `lastNonzero` via `lastNonzeroProp`. -/
theorem lastNonzero_some_iff [LawfulBEq R] {p : CPolynomial R} {k} :
    p.lastNonzero = some k ↔ (p[k] ≠ 0 ∧ (∀ j, (hj : j < p.size) → j > k → p[j] = 0)) := by
  constructor
  · apply lastNonzero_spec
  intro h_prop
  have ⟨ k', h_some'⟩ := lastNonzero_some k.is_lt h_prop.left
  have k_is_k' := lastNonzero_unique (lastNonzero_spec h_some') h_prop
  rwa [← k_is_k']

/-- eliminator for `p.lastNonzero`, e.g. use with the induction tactic as follows:
  ```
  induction p using lastNonzero_induct with
  | case1 p h_none h_all_zero => ...
  | case2 p k h_some h_nonzero h_max => ...
  ```
-/
theorem lastNonzero_induct [LawfulBEq R] {motive : CPolynomial R → Prop}
    (case1 : ∀ p, p.lastNonzero = none → (∀ i, (hi : i < p.size) → p[i] = 0) → motive p)
  (case2 : ∀ p : CPolynomial R, ∀ k : Fin p.size, p.lastNonzero = some k → p[k] ≠ 0 →
    (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0) → motive p)
  (p : CPolynomial R) : motive p := by
  by_cases h : ∀ i, (hi : i < p.size) → p[i] = 0
  · exact case1 p (lastNonzero_none h) h
  · push_neg at h; rcases h with ⟨ i, hi, h ⟩
    obtain ⟨ k, h_some ⟩ := lastNonzero_some hi h
    have ⟨ h_nonzero, h_max ⟩ := lastNonzero_spec h_some
    exact case2 p k h_some h_nonzero h_max

/-- eliminator for `p.trim`; use with the induction tactic as follows:
  ```
  induction p using induct with
  | case1 p h_empty h_all_zero => ...
  | case2 p k h_extract h_nonzero h_max => ...
  ```
-/
theorem induct [LawfulBEq R] {motive : CPolynomial R → Prop}
    (case1 : ∀ p, p.trim = #[] → (∀ i, (hi : i < p.size) → p[i] = 0) → motive p)
  (case2 : ∀ p : CPolynomial R, ∀ k : Fin p.size, p.trim = p.extract 0 (k + 1)
    → p[k] ≠ 0 → (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0) → motive p)
  (p : CPolynomial R) : motive p := by induction p using lastNonzero_induct with
  | case1 p h_none h_all_zero =>
    have h_empty : p.trim = #[] := by unfold trim; rw [h_none]
    exact case1 p h_empty h_all_zero
  | case2 p k h_some h_nonzero h_max =>
    have h_extract : p.trim = p.extract 0 (k + 1) := by unfold trim; rw [h_some]
    exact case2 p k h_extract h_nonzero h_max

/-- eliminator for `p.trim`; e.g. use for case distinction as follows:
  ```
  rcases (Trim.elim p) with ⟨ h_empty, h_all_zero ⟩ | ⟨ k, h_extract, h_nonzero, h_max ⟩
  ```
-/
theorem elim [LawfulBEq R] (p : CPolynomial R) :
    (p.trim = #[] ∧  (∀ i, (hi : i < p.size) → p[i] = 0))
    ∨ (∃ k : Fin p.size,
        p.trim = p.extract 0 (k + 1)
      ∧ p[k] ≠ 0
      ∧ (∀ j : ℕ, (hj : j < p.size) → j > k → p[j] = 0)) := by induction p using induct with
  | case1 p h_empty h_all_zero => left; exact ⟨h_empty, h_all_zero⟩
  | case2 p k h_extract h_nonzero h_max => right; exact ⟨k, h_extract, h_nonzero, h_max⟩

theorem size_eq_degree (p : CPolynomial R) : p.trim.size = p.degree := by
  unfold trim degree
  match h : p.lastNonzero with
  | none => simp
  | some i => simp [Fin.is_lt, Nat.succ_le_of_lt]

theorem size_le_size (p : CPolynomial R) : p.trim.size ≤ p.size := by
  unfold trim
  match h : p.lastNonzero with
  | none => simp
  | some i => simp [Array.size_extract]

attribute [simp] Array.getElem?_eq_none

theorem coeff_eq_getElem_of_lt [LawfulBEq R] {p : CPolynomial R} {i} (hi : i < p.size) :
    p.trim.coeff i = p[i] := by
  induction p using induct with
  | case1 p h_empty h_all_zero =>
    specialize h_all_zero i hi
    simp [h_empty, h_all_zero]
  | case2 p k h_extract h_nonzero h_max =>
    simp [h_extract]
    -- split between i > k and i <= k
    have h_size : k + 1 = (p.extract 0 (k + 1)).size := by
      simp [Array.size_extract]
      exact Nat.succ_le_of_lt k.is_lt
    rcases (Nat.lt_or_ge k i) with hik | hik
    · have hik' : i ≥ (p.extract 0 (k + 1)).size := by linarith
      rw [Array.getElem?_eq_none hik', Option.getD_none]
      exact h_max i hi hik |> Eq.symm
    · have hik' : i < (p.extract 0 (k + 1)).size := by linarith
      rw [Array.getElem?_eq_getElem hik', Option.getD_some, Array.getElem_extract]
      simp only [zero_add]

theorem coeff_eq_coeff [LawfulBEq R] (p : CPolynomial R) (i : ℕ) :
    p.trim.coeff i = p.coeff i := by
  rcases (Nat.lt_or_ge i p.size) with hi | hi
  · rw [coeff_eq_getElem_of_lt hi]
    simp [hi]
  · have hi' : i ≥ p.trim.size := by linarith [size_le_size p]
    simp [hi, hi']

lemma coeff_eq_getElem {p : CPolynomial Q} {i} (hp : i < p.size) :
    p.coeff i = p[i] := by
  simp [hp]

/-- Equivalence relation: two polynomials are equivalent if all coefficients agree. -/
def equiv (p q : CPolynomial R) : Prop :=
  ∀ i, p.coeff i = q.coeff i

lemma coeff_eq_zero {p : CPolynomial Q} :
    (∀ i, (hi : i < p.size) → p[i] = 0) ↔ ∀ i, p.coeff i = 0 := by
  constructor <;> intro h i
  · cases Nat.lt_or_ge i p.size <;> simp [*]
  · intro hi; specialize h i; simp [hi] at h; assumption

lemma eq_degree_of_equiv [LawfulBEq R] {p q : CPolynomial R} :
    equiv p q → p.degree = q.degree := by
  unfold equiv degree
  intro h_equiv
  induction p using lastNonzero_induct with
  | case1 p h_none_p h_all_zero =>
    have h_zero_p : ∀ i, p.coeff i = 0 := coeff_eq_zero.mp h_all_zero
    have h_zero_q : ∀ i, q.coeff i = 0 := by intro i; rw [← h_equiv, h_zero_p]
    have h_none_q : q.lastNonzero = none := lastNonzero_none (coeff_eq_zero.mpr h_zero_q)
    rw [h_none_p, h_none_q]
  | case2 p k h_some_p h_nonzero_p h_max_p =>
    have h_equiv_k := h_equiv k
    have k_lt_q : k < q.size := by
      by_contra h_not_lt
      have h_ge := Nat.le_of_not_lt h_not_lt
      simp [h_ge] at h_equiv_k
      contradiction
    simp [k_lt_q] at h_equiv_k
    have h_nonzero_q : q[k.val] ≠ 0 := by rwa [← h_equiv_k]
    have h_max_q : ∀ j, (hj : j < q.size) → j > k → q[j] = 0 := by
      intro j hj j_gt_k
      have h_eq := h_equiv j
      simp [hj] at h_eq
      rw [← h_eq]
      rcases Nat.lt_or_ge j p.size with hj | hj
      · simp [hj, h_max_p j hj j_gt_k]
      · simp [hj]
    have h_some_q : q.lastNonzero = some ⟨ k, k_lt_q ⟩ :=
      lastNonzero_some_iff.mpr ⟨ h_nonzero_q, h_max_q ⟩
    rw [h_some_p, h_some_q]

theorem eq_of_equiv [LawfulBEq R] {p q : CPolynomial R} : equiv p q → p.trim = q.trim := by
  unfold equiv
  intro h
  ext
  · rw [size_eq_degree, size_eq_degree]
    apply eq_degree_of_equiv h
  rw [← coeff_eq_getElem, ← coeff_eq_getElem]
  rw [coeff_eq_coeff, coeff_eq_coeff, h _]

theorem trim_equiv [LawfulBEq R] (p : CPolynomial R) : equiv p.trim p := by
  apply coeff_eq_coeff

theorem trim_twice [LawfulBEq R] (p : CPolynomial R) : p.trim.trim = p.trim := by
  apply eq_of_equiv
  apply trim_equiv

theorem canonical_empty : (CPolynomial.mk (R:=R) #[]).trim = #[] := by
  have : (CPolynomial.mk (R:=R) #[]).lastNonzero = none := by
    simp [lastNonzero];
    apply Array.findIdxRev?_empty_none
    rfl
  rw [trim, this]

theorem canonical_of_size_zero {p : CPolynomial R} : p.size = 0 → p.trim = p := by
  intro h
  suffices h_empty : p = #[] by rw [h_empty]; exact canonical_empty
  exact Array.eq_empty_of_size_eq_zero h

theorem canonical_nonempty_iff [LawfulBEq R] {p : CPolynomial R} (hp : p.size > 0) :
    p.trim = p ↔ p.lastNonzero = some ⟨ p.size - 1, Nat.pred_lt_self hp ⟩ := by
  unfold trim
  induction p using lastNonzero_induct with
  | case1 p h_none h_all_zero =>
    simp [h_none]
    by_contra h_empty
    subst h_empty
    contradiction
  | case2 p k h_some h_nonzero h_max =>
    simp [h_some]
    constructor
    · intro h
      ext
      have : p ≠ #[] := Array.ne_empty_of_size_pos hp
      simp [this] at h
      have : k + 1 ≤ p.size := Nat.succ_le_of_lt k.is_lt
      have : p.size = k + 1 := Nat.le_antisymm h this
      simp [this]
    · intro h
      have : k + 1 = p.size := by rw [h]; exact Nat.succ_pred_eq_of_pos hp
      rw [this]
      right
      exact le_refl _

theorem lastNonzero_last_iff [LawfulBEq R] {p : CPolynomial R} (hp : p.size > 0) :
    p.lastNonzero = some ⟨ p.size - 1, Nat.pred_lt_self hp ⟩ ↔ p.getLast hp ≠ 0 := by
  induction p using lastNonzero_induct with
  | case1 => simp [Array.getLast, *]
  | case2 p k h_some h_nonzero h_max =>
    simp only [h_some, Option.some_inj, Array.getLast]
    constructor
    · intro h
      have : k = p.size - 1 := by rw [h]
      conv => lhs; congr; case i => rw [← this]
      assumption
    · intro h
      rcases Nat.lt_trichotomy k (p.size - 1) with h_lt | h_eq | h_gt
      · specialize h_max (p.size - 1) (Nat.pred_lt_self hp) h_lt
        contradiction
      · ext; assumption
      · have : k < p.size := k.is_lt
        have : k ≥ p.size := Nat.le_of_pred_lt h_gt
        linarith

theorem canonical_iff [LawfulBEq R] {p : CPolynomial R} :
    p.trim = p ↔ ∀ hp : p.size > 0, p.getLast hp ≠ 0 := by
  constructor
  · intro h hp
    rwa [← lastNonzero_last_iff hp, ← canonical_nonempty_iff hp]
  · rintro h
    rcases Nat.eq_zero_or_pos p.size with h_zero | hp
    · exact canonical_of_size_zero h_zero
    · rw [canonical_nonempty_iff hp, lastNonzero_last_iff hp]
      exact h hp

theorem non_zero_map [LawfulBEq R] (f : R → R) (hf : ∀ r, f r = 0 → r = 0) (p : CPolynomial R) :
    let fp := CPolynomial.mk (p.map f);
  p.trim = p → fp.trim = fp := by
  intro fp p_canon
  by_cases hp : p.size > 0
  -- positive case
  · apply canonical_iff.mpr
    intro hfp
    have h_nonzero := canonical_iff.mp p_canon hp
    have : fp.getLast hfp = f (p.getLast hp) := by simp [Array.getLast, fp]
    rw [this]
    by_contra h_zero
    specialize hf (p.getLast hp) h_zero
    contradiction
  -- zero case
  have : p.size = 0 := by linarith
  have : fp.size = 0 := by simp [this, fp]
  apply canonical_of_size_zero this

/-- Canonical polynomials enjoy a stronger extensionality theorem:
  they just need to agree at all coefficients (without assuming equal sizes)
-/
theorem canonical_ext [LawfulBEq R] {p q : CPolynomial R} (hp : p.trim = p) (hq : q.trim = q) :
    equiv p q → p = q := by
  intro h_equiv
  rw [← hp, ← hq]
  exact eq_of_equiv h_equiv

end Trim

section Operations

variable {S : Type*}

-- p(x) = a_0 + a_1 x + a_2 x^2 + ... + a_n x^n

-- eval₂ f x p = f(a_0) + f(a_1) x + f(a_2) x^2 + ... + f(a_n) x^n

/-- Evaluates a `CPolynomial` at `x : S` using a ring homomorphism `f : R →+* S`.

  Computes `f(a₀) + f(a₁) * x + f(a₂) * x² + ...` where `aᵢ` are the coefficients.

  TODO: define an efficient version of this with caching -/
def eval₂ [Semiring S] (f : R →+* S) (x : S) (p : CPolynomial R) : S :=
  p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + f a * x ^ i) 0

/-- Evaluates a `CPolynomial` at a given value -/
@[inline, specialize]
def eval (x : R) (p : CPolynomial R) : R :=
  p.eval₂ (RingHom.id R) x

/-- Raw addition: pointwise sum of coefficient arrays (padded to equal length).

  The result may have trailing zeros and should be trimmed for canonical form. -/
@[inline, specialize]
def addRaw (p q : CPolynomial R) : CPolynomial R :=
  let ⟨p', q'⟩ := Array.matchSize p q 0
  .mk (Array.zipWith (· + ·) p' q' )

/-- Addition of two `CPolynomial`s, with result trimmed. -/
@[inline, specialize]
def add (p q : CPolynomial R) : CPolynomial R :=
  addRaw p q |> trim

/-- Scalar multiplication: multiplies each coefficient by `r`. -/
@[inline, specialize]
def smul (r : R) (p : CPolynomial R) : CPolynomial R :=
  .mk (Array.map (fun a => r * a) p)

/-- Raw scalar multiplication by a natural number (may have trailing zeros). -/
@[inline, specialize]
def nsmulRaw (n : ℕ) (p : CPolynomial R) : CPolynomial R :=
  .mk (Array.map (fun a => n * a) p)

/-- Scalar multiplication of `CPolynomial` by a natural number, with result trimmed. -/
@[inline, specialize]
def nsmul (n : ℕ) (p : CPolynomial R) : CPolynomial R :=
  nsmulRaw n p |> trim

/-- Negation of a `CPolynomial`. -/
@[inline, specialize]
def neg (p : CPolynomial R) : CPolynomial R := p.map (fun a => -a)

/-- Subtraction of two `CPolynomial`s. -/
@[inline, specialize]
def sub (p q : CPolynomial R) : CPolynomial R := p.add q.neg

/-- Multiplication by `X^i`: shifts coefficients right by `i` positions (prepends `i` zeros). -/
@[inline, specialize]
def mulPowX (i : Nat) (p : CPolynomial R) : CPolynomial R := .mk (Array.replicate i 0 ++ p)

/-- Multiplication of a `CPolynomial` by `X`, reduces to `mulPowX 1`. -/
@[inline, specialize]
def mulX (p : CPolynomial R) : CPolynomial R := p.mulPowX 1

/-- Multiplication using the naive `O(n²)` algorithm: `Σᵢ (aᵢ * q) * X^i`. -/
@[inline, specialize]
def mul (p q : CPolynomial R) : CPolynomial R :=
  p.zipIdx.foldl (fun acc ⟨a, i⟩ => acc.add <| (smul a q).mulPowX i) (mk #[])

/-- Exponentiation of a `CPolynomial` by a natural number `n` via repeated multiplication. -/
@[inline, specialize]
def pow (p : CPolynomial R) (n : Nat) : CPolynomial R := (mul p)^[n] (C 1)

-- TODO: define repeated squaring version of `pow`

instance : Zero (CPolynomial R) := ⟨#[]⟩

instance : One (CPolynomial R) := ⟨CPolynomial.C 1⟩

instance : Add (CPolynomial R) := ⟨CPolynomial.add⟩

instance : SMul R (CPolynomial R) := ⟨CPolynomial.smul⟩

instance : SMul ℕ (CPolynomial R) := ⟨nsmul⟩

instance : Neg (CPolynomial R) := ⟨CPolynomial.neg⟩

instance : Sub (CPolynomial R) := ⟨CPolynomial.sub⟩

instance : Mul (CPolynomial R) := ⟨CPolynomial.mul⟩

instance : Pow (CPolynomial R) Nat := ⟨CPolynomial.pow⟩

instance : NatCast (CPolynomial R) := ⟨fun n => CPolynomial.C (n : R)⟩

instance : IntCast (CPolynomial R) := ⟨fun n => CPolynomial.C (n : R)⟩

/-- Upper bound on degree: `size - 1` if non-empty, `⊥` if empty. -/
def degreeBound (p : CPolynomial R) : WithBot Nat :=
  match p.size with
  | 0 => ⊥
  | .succ n => n

/-- Convert `degreeBound` to a natural number by sending `⊥` to `0`. -/
def natDegreeBound (p : CPolynomial R) : Nat :=
  (degreeBound p).getD 0

/-- Check if a `CPolynomial` is monic, i.e. its leading coefficient is 1. -/
def monic (p : CPolynomial R) : Bool := p.leadingCoeff == 1

/-- Division with remainder by a monic polynomial using polynomial long division. -/
def divModByMonicAux [Field R] (p : CPolynomial R) (q : CPolynomial R) :
    CPolynomial R × CPolynomial R :=
  go (p.size - q.size) p q
where
  go : Nat → CPolynomial R → CPolynomial R → CPolynomial R × CPolynomial R
  | 0, p, _ => ⟨0, p⟩
  | n+1, p, q =>
      let k := p.size - q.size -- k should equal n, this is technically unneeded
      let q' := C p.leadingCoeff * (q * X.pow k)
      let p' := (p - q').trim
      let (e, f) := go n p' q
      -- p' = q * e + f
      -- Thus p = p' + q' = q * e + f + p.leadingCoeff * q * X^n
      -- = q * (e + p.leadingCoeff * X^n) + f
      ⟨e + C p.leadingCoeff * X^k, f⟩

/-- Division of `p : CPolynomial R` by a monic `q : CPolynomial R`. -/
def divByMonic [Field R] (p : CPolynomial R) (q : CPolynomial R) :
    CPolynomial R :=
  (divModByMonicAux p q).1

/-- Modulus of `p : CPolynomial R` by a monic `q : CPolynomial R`. -/
def modByMonic [Field R] (p : CPolynomial R) (q : CPolynomial R) :
    CPolynomial R :=
  (divModByMonicAux p q).2

/-- Division of two `CPolynomial`s. -/
def div [Field R] (p q : CPolynomial R) : CPolynomial R :=
  (C (q.leadingCoeff)⁻¹ • p).divByMonic (C (q.leadingCoeff)⁻¹ * q)

/-- Modulus of two `CPolynomial`s. -/
def mod [Field R] (p q : CPolynomial R) : CPolynomial R :=
  (C (q.leadingCoeff)⁻¹ • p).modByMonic (C (q.leadingCoeff)⁻¹ * q)

instance [Field R] : Div (CPolynomial R) := ⟨CPolynomial.div⟩

instance [Field R] : Mod (CPolynomial R) := ⟨CPolynomial.mod⟩

/-- Pseudo-division by `X`: removes the constant term and shifts remaining coefficients left. -/
def divX (p : CPolynomial R) : CPolynomial R := p.extract 1 p.size

variable (p q r : CPolynomial R)

-- some helper lemmas to characterize p + q

lemma matchSize_size_eq {p q : CPolynomial Q} :
    let (p', q') := Array.matchSize p q 0
    p'.size = q'.size := by
  change (Array.rightpad _ _ _).size = (Array.rightpad _ _ _).size
  rw [Array.size_rightpad, Array.size_rightpad]
  omega

lemma matchSize_size {p q : CPolynomial Q} :
    let (p', _) := Array.matchSize p q 0
    p'.size = max p.size q.size := by
  change (Array.rightpad _ _ _).size = max (Array.size _) (Array.size _)
  rw [Array.size_rightpad]
  omega

lemma zipWith_size {R} {f : R → R → R} {a b : Array R} (h : a.size = b.size) :
    (Array.zipWith f a b).size = a.size := by
  simp; omega

-- TODO we could generalize the next few lemmas to matchSize + zipWith f for any f

theorem add_size {p q : CPolynomial Q} : (addRaw p q).size = max p.size q.size := by
  change (Array.zipWith _ _ _ ).size = max p.size q.size
  rw [zipWith_size matchSize_size_eq, matchSize_size]

-- coeff on list concatenations
omit [BEq R] in
lemma concat_coeff₁ (i : ℕ) : i < p.size →
    (p ++ q).coeff i = p.coeff i := by simp; grind

omit [BEq R] in
lemma concat_coeff₂ (i : ℕ) : i ≥ p.size →
    (p ++ q).coeff i = q.coeff (i - p.size) := by simp; grind

theorem add_coeff {p q : CPolynomial Q} {i : ℕ} (hi : i < (addRaw p q).size) :
    (addRaw p q)[i] = p.coeff i + q.coeff i := by
  simp [addRaw]
  by_cases hi' : i < p.size <;> by_cases hi'' : i < q.size <;> simp_all

theorem add_coeff? (p q : CPolynomial Q) (i : ℕ) :
    (addRaw p q).coeff i = p.coeff i + q.coeff i := by
  rcases (Nat.lt_or_ge i (addRaw p q).size) with h_lt | h_ge
  · rw [← add_coeff h_lt]; simp [h_lt]
  have h_lt' : i ≥ max p.size q.size := by rwa [← add_size]
  have h_p : i ≥ p.size := by omega
  have h_q : i ≥ q.size := by omega
  simp [h_ge, h_p, h_q]

lemma add_equiv_raw [LawfulBEq R] (p q : CPolynomial R) :
    Trim.equiv (p.add q) (p.addRaw q) := by
  unfold Trim.equiv add
  exact Trim.coeff_eq_coeff (p.addRaw q)

omit [BEq R] in
lemma smul_equiv : ∀ (i : ℕ) (r : R),
    (smul r p).coeff i = r * (p.coeff i) := by
  intro i r
  unfold smul mk coeff
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi]

lemma nsmulRaw_equiv [LawfulBEq R] : ∀ (n i : ℕ),
    (nsmulRaw n p).trim.coeff i = n * p.trim.coeff i := by
  intro n i
  unfold nsmulRaw
  repeat rw [Trim.coeff_eq_coeff]
  unfold mk
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi]

lemma mul_pow_assoc : ∀ (p : CPolynomial R) (n : ℕ),
    ∀ (q : CPolynomial R) (m l : ℕ),
  l + m = n →
  p.mul^[n] q = p.mul^[m] (p.mul^[l] q) := by
  intro p n
  induction n with
  | zero =>
    intro q m l h_sizes
    rw [Nat.add_eq_zero_iff] at h_sizes
    obtain ⟨hl, hm⟩ := h_sizes
    rw [hl, hm]
    simp

  | succ n₀ ih =>
    intro q m l h_sizes
    cases l with
    | zero =>
      simp at h_sizes
      rw [h_sizes]
      simp

    | succ l₀ =>
      have h_sizes_simp : l₀ + m = n₀ := by linarith
      clear h_sizes
      simp

      rw [ih (p.mul q) m l₀ h_sizes_simp]

lemma mul_pow_succ (p q : CPolynomial R) (n : ℕ):
    p.mul^[n + 1] q = p.mul (p.mul^[n] q) := by
  rw [mul_pow_assoc p (n+1) q 1 n] <;> simp

omit [BEq R] in
lemma neg_coeff : ∀ (p : CPolynomial R) (i : ℕ), p.neg.coeff i = - p.coeff i := by
  intro p i
  unfold neg coeff
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi]

lemma trim_add_trim [LawfulBEq R] (p q : CPolynomial R) : p.trim + q = p + q := by
  apply Trim.eq_of_equiv
  intro i
  rw [add_coeff?, add_coeff?, Trim.coeff_eq_coeff]

-- algebra theorems about addition

omit [Ring Q] in
@[simp] theorem zero_def : (0 : CPolynomial Q) = #[] := rfl

theorem add_comm : p + q = q + p := by
  apply congrArg trim
  ext
  · simp only [add_size]; omega
  · simp only [add_coeff]
    apply _root_.add_comm

/-- A polynomial is canonical if it has no trailing zeros. -/
def canonical (p : CPolynomial R) := p.trim = p

theorem zero_canonical : (0 : CPolynomial R).trim = 0 := Trim.canonical_empty

theorem zero_add (hp : p.canonical) : 0 + p = p := by
  rw (occs := .pos [2]) [← hp]
  apply congrArg trim
  ext <;> simp [add_size, add_coeff, *]

theorem add_zero (hp : p.canonical) : p + 0 = p := by
  rw [add_comm, zero_add p hp]

theorem add_assoc [LawfulBEq R] : p + q + r = p + (q + r) := by
  change (addRaw p q).trim + r = p + (addRaw q r).trim
  rw [trim_add_trim, add_comm p, trim_add_trim, add_comm _ p]
  apply congrArg trim
  ext i
  · simp only [add_size]; omega
  · simp only [add_coeff, add_coeff?]
    apply _root_.add_assoc

theorem nsmul_zero [LawfulBEq R] (p : CPolynomial R) : nsmul 0 p = 0 := by
  suffices (nsmulRaw 0 p).lastNonzero = none by simp [nsmul, trim, *]
  apply Trim.lastNonzero_none
  intros; unfold nsmulRaw
  simp only [Nat.cast_zero, zero_mul, Array.getElem_map]

theorem nsmulRawSucc (n : ℕ) (p : CPolynomial Q) :
    nsmulRaw (n + 1) p = addRaw (nsmulRaw n p) p := by
  unfold nsmulRaw
  ext
  · simp [add_size]
  next i _ hi =>
    simp [add_size] at hi
    simp [add_coeff, hi]
    rw [_root_.add_mul (R:=Q) n 1 p[i], one_mul]

theorem nsmul_succ [LawfulBEq R] (n : ℕ) {p : CPolynomial R} : nsmul (n + 1) p = nsmul n p + p := by
  unfold nsmul
  rw [trim_add_trim]
  apply congrArg trim
  apply nsmulRawSucc

theorem neg_trim [LawfulBEq R] (p : CPolynomial R) : p.trim = p → (-p).trim = -p := by
  apply Trim.non_zero_map
  simp

theorem neg_add_cancel [LawfulBEq R] (p : CPolynomial R) : -p + p = 0 := by
  rw [← zero_canonical]
  apply Trim.eq_of_equiv; unfold Trim.equiv; intro i
  rw [add_coeff?]
  rcases (Nat.lt_or_ge i p.size) with hi | hi <;> simp [hi, Neg.neg, neg]

/- Aristotle failed to find a proof. -/
theorem mul_assoc [LawfulBEq R] (p q r : CPolynomial R) : p * q * r = p * (q * r) := by sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

lemma mulPowX_coeff (n : ℕ) (p : CPolynomial R) (i : ℕ) :
    (mulPowX n p).coeff i = if i < n then 0 else p.coeff (i - n) := by
      -- By definition of `mulPowX`, the coefficient of `mulPowX n p` at position `i` is zero if `i < n`, and `p.coeff (i - n)` otherwise.
      simp [CompPoly.CPolynomial.mulPowX];
      grind

lemma add_coeff_correct [LawfulBEq R] (p q : CPolynomial R) (i : ℕ) :
    (p + q).coeff i = p.coeff i + q.coeff i := by
      -- By definition of polynomial addition, the coefficient of X^i in p + q is the sum of the coefficients of X^i in p and q. This follows directly from the definition of `addRaw` and the fact that `trim` is idempotent.
      have h_coeff : (p + q).coeff i = (addRaw p q).coeff i := by
        -- By definition of `trim`, we know that `trim (addRaw p q)` is the trimmed version of `addRaw p q`. Therefore, their coefficients are equal.
        apply Trim.coeff_eq_coeff;
      exact h_coeff.trans ( add_coeff? p q i )

lemma smul_coeff_correct (p : CPolynomial R) (r : R) (i : ℕ) :
    (smul r p).coeff i = r * p.coeff i := by
      exact?

lemma foldl_add_coeff [LawfulBEq R] {α : Type*} (l : List α) (f : α → CPolynomial R) (init : CPolynomial R) (k : ℕ) :
    (l.foldl (fun acc x => acc + f x) init).coeff k = init.coeff k + (l.map (fun x => (f x).coeff k)).sum := by
      -- Apply the linearity of the coefficient function to each step of the fold.
      have h_linear : ∀ (acc : CPolynomial R) (x : α), (acc + f x).coeff k = acc.coeff k + (f x).coeff k := by
        exact?
      generalize_proofs at *;
      induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ add_assoc ];
      grind

lemma coeff_C_zero (k : ℕ) : (C (0 : R)).coeff k = 0 := by
  -- By definition of `CompPoly.CPolynomial.C`, we know that `CompPoly.CPolynomial.C 0` is the constant polynomial with coefficient 0.
  simp [CompPoly.CPolynomial.C]

lemma mul_term_coeff (q : CPolynomial R) (x : R × ℕ) (k : ℕ) :
    ((smul x.1 q).mulPowX x.2).coeff k = if k < x.2 then 0 else x.1 * q.coeff (k - x.2) := by
      -- By definition of `mulPowX`, the coefficient of the polynomial at position `k` is zero if `k < x.2` and `x.1 * q.coeff (k - x.2)` otherwise.
      have h_coeff : ∀ k, (mulPowX x.2 (smul x.1 q)).coeff k = if k < x.2 then 0 else (smul x.1 q).coeff (k - x.2) := by
        -- By definition of `mulPowX`, the coefficient of `k` in `mulPowX x.2 (smul x.1 q)` is zero if `k < x.2` and `x.1 * q.coeff (k - x.2)` otherwise.
        intros k
        simp [mulPowX];
        grind;
      -- By definition of `smul`, the coefficient of the polynomial at position `k` is `x.1 * q.coeff k`.
      have h_smul_coeff : ∀ k, (smul x.1 q).coeff k = x.1 * q.coeff k := by
        exact?;
      rw [ h_coeff, h_smul_coeff ]

lemma Array.foldl_eq_foldl_toList {α β : Type*} (f : β → α → β) (init : β) (as : Array α) :
    as.foldl f init = as.toList.foldl f init := by
      grind

lemma mul_eq_foldl (p q : CPolynomial R) :
    p * q = p.zipIdx.foldl (fun acc x => acc + (smul x.1 q).mulPowX x.2) (C 0) := rfl

lemma List_map_congr {α β} {l : List α} {f g : α → β} (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  exact?

lemma mul_coeff_sum [LawfulBEq R] (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (p.zipIdx.toList.map (fun (x : R × ℕ) => if k < x.2 then 0 else x.1 * q.coeff (k - x.2))).sum := by
  rw [mul_eq_foldl]
  rw [Array.foldl_eq_foldl_toList]
  rw [foldl_add_coeff]
  simp only [coeff_C_zero, AddZeroClass.zero_add]
  apply congr_arg List.sum
  apply List_map_congr
  intro x hx
  rw [mul_term_coeff]

lemma mul_coeff_sum_aux [LawfulBEq R] (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = (p.zipIdx.toList.map (fun (x : R × ℕ) => if k < x.2 then 0 else x.1 * q.coeff (k - x.2))).sum := by
  rw [mul_eq_foldl]
  rw [Array.foldl_eq_foldl_toList]
  rw [foldl_add_coeff]
  simp only [coeff_C_zero, AddZeroClass.zero_add]
  apply congr_arg List.sum
  apply List_map_congr
  intro x hx
  rw [mul_term_coeff]

lemma sum_zipIdx_map (p : CPolynomial R) (g : ℕ → R) :
    (p.zipIdx.toList.map (fun x => x.1 * g x.2)).sum = ((List.range p.size).map (fun i => p.coeff i * g i)).sum := by
      -- Since the zipIdx of p is just the list of pairs (coeff, index) for each coefficient in p, and the range of the size of p is the list of indices from 0 to the size of p minus one, the two lists are essentially the same.
      have h_zipIdx_range : List.map (fun (x : R × ℕ) => x.1 * g x.2) (Array.zipIdx p).toList = List.map (fun (i : ℕ) => p.coeff i * g i) (List.range p.size) := by
        refine' List.ext_get _ _ <;> aesop;
      rw [h_zipIdx_range]

lemma mul_coeff_sum_range [LawfulBEq R] (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = ((List.range p.size).map (fun i => if k < i then 0 else p.coeff i * q.coeff (k - i))).sum := by
  rw [mul_coeff_sum_aux]
  let g := fun i => if k < i then 0 else q.coeff (k - i)
  have h_eq : (fun (x : R × ℕ) => if k < x.2 then 0 else x.1 * q.coeff (k - x.2)) = (fun x => x.1 * g x.2) := by
    ext x
    dsimp [g]
    split_ifs <;> simp
  rw [h_eq]
  rw [sum_zipIdx_map]
  congr
  ext i
  dsimp [g]
  split_ifs <;> simp

lemma sum_range_le {f : ℕ → R} {n m : ℕ} (hnm : n ≤ m) (h : ∀ i, n ≤ i → i < m → f i = 0) :
    ((List.range m).map f).sum = ((List.range n).map f).sum := by
      -- By definition of sum, we can split the sum into two parts: the sum up to n and the sum from n to m.
      have h_split : (List.map f (List.range m)).sum = (List.map f (List.range n)).sum + (List.map f (List.drop n (List.range m))).sum := by
        -- By definition of sum, we can split the sum into two parts: the sum up to n and the sum from n to m. This follows from the associativity of addition.
        have h_split : (List.map f (List.range m)).sum = (List.map f (List.take n (List.range m) ++ List.drop n (List.range m))).sum := by
          rw [ List.take_append_drop ];
        rw [ h_split, List.map_append, List.sum_append ];
        grind;
      -- Since $f$ is zero for all $i$ in the range $n$ to $m$, the list obtained by dropping $n$ elements from the range $m$ is all zeros. We can prove this by showing that every element in the list is zero.
      have h_zero_elements : ∀ i ∈ List.drop n (List.range m), f i = 0 := by
        intro i hi;
        rw [ List.mem_iff_get ] at hi;
        grind;
      -- Since every element in the list is zero, the mapped list is all zeros.
      have h_map_zero : List.map f (List.drop n (List.range m)) = List.replicate (List.length (List.drop n (List.range m))) 0 := by
        exact?;
      aesop

lemma mul_coeff_eq_sum_range [LawfulBEq R] (p q : CPolynomial R) (k : ℕ) :
    (p * q).coeff k = ((List.range (k + 1)).map (fun i => p.coeff i * q.coeff (k - i))).sum := by
      rw [mul_coeff_sum_range];
      -- Apply the sum_range_le lemma with n = k + 1 and m = p.size.
      have h_sum_eq : ((List.range p.size).map (fun i => if k < i then 0 else p.coeff i * q.coeff (k - i))).sum = ((List.range (k + 1)).map (fun i => if k < i then 0 else p.coeff i * q.coeff (k - i))).sum := by
        -- Apply the lemma sum_range_le with n = k+1 and m = p.size, given that n ≤ m.
        have h_sum_eq : ∀ i, k + 1 ≤ i → i < p.size → (if k < i then 0 else p.coeff i * q.coeff (k - i)) = 0 := by
          exact fun i hi₁ hi₂ => if_pos hi₁;
        by_cases h : k + 1 ≤ p.size;
        · -- Apply the sum_range_le lemma with n = k+1 and m = p.size, given that n ≤ m and the condition holds for i ≥ n.
          apply sum_range_le h (fun i hi₁ hi₂ => h_sum_eq i hi₁ hi₂);
        · -- Since $k + 1 > \text{size}(p)$, the range up to $k + 1$ is the same as the range up to $\text{size}(p)$.
          have h_range_eq : List.range (k + 1) = List.range (Array.size p) ++ List.map (fun i => i + Array.size p) (List.range (k + 1 - Array.size p)) := by
            refine' List.ext_get _ _ <;> simp +decide [ List.get ];
            · rw [ Nat.add_sub_of_le ( le_of_not_ge h ) ];
            · intro n hn h₂; rw [ List.getElem_append ] ; aesop;
          rw [ h_range_eq, List.map_append, List.sum_append ];
          simp +decide [ List.sum_map_eq_nsmul_single 0, h ];
      rw [ h_sum_eq ];
      congr! 1;
      exact List.map_congr_left fun i hi => by rw [ if_neg ( by linarith [ List.mem_range.mp hi ] ) ] ;

lemma sum_range_reverse {f : ℕ → R} (k : ℕ) :
    ((List.range (k + 1)).map f).sum = ((List.range (k + 1)).map (fun i => f (k - i))).sum := by
      -- By definition of `List.reverse`, we can reverse the list and then map `f` to get the same result.
      have h_reverse : List.map (fun i => f (k - i)) (List.range (k + 1)) = List.map f (List.reverse (List.range (k + 1))) := by
        refine' List.ext_get _ _ <;> simp +decide [ List.getElem_range ];
      -- By the properties of summation, reversing the list doesn't change the sum.
      have h_sum_reverse : ∀ (l : List R), List.sum (List.reverse l) = List.sum l := by
        exact?;
      convert h_sum_reverse ( List.map f ( List.range ( k + 1 ) ) ) |> Eq.symm using 1;
      convert congr_arg List.sum h_reverse using 1;
      rw [ List.map_reverse ]

#eval (let p : CPolynomial ℤ := #[]; let q : CPolynomial ℤ := #[1]; (p * q, q * p))

theorem mul_comm_false : ¬ (∀ (p q : CPolynomial ℤ), p * q = q * p) := by
  intro h
  let p : CPolynomial ℤ := #[]
  let q : CPolynomial ℤ := #[1]
  have h_eq := h p q
  have h_ne : p * q ≠ q * p := by native_decide
  contradiction

end AristotleLemmas

theorem mul_comm [CommRing R] [LawfulBEq R] (p q : CPolynomial R) : p * q = q * p := by
  have := @mul_comm_false;
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  simp +zetaDelta at *;
  refine' ⟨ ULift ℤ, inferInstance, inferInstance, _, _, _, _ ⟩;
  · refine' { .. };
    norm_num +zetaDelta at *;
  · exists #[], #[1];
    native_decide +revert;
  · exact ⟨ inferInstance ⟩;
  · refine' ⟨ _, _, _ ⟩;
    exact #[1];
    exact #[];
    native_decide +revert

-/
theorem mul_comm [CommRing R] [LawfulBEq R] (p q : CPolynomial R) : p * q = q * p := by sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Multiplication by the empty polynomial (which represents zero) returns `#[0]` (which also represents zero but has size 1), not `#[]`.
-/
open CompPoly CPolynomial

variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]

lemma mul_empty (q : CPolynomial R) : mul #[] q = #[0] := by
  exact?

/-
Adding `#[0]` to `#[0]` results in `#[]` because `add` trims the result.
-/
lemma add_zero_zero {R : Type*} [Ring R] [BEq R] [LawfulBEq R] : CompPoly.CPolynomial.add (#[0] : CompPoly.CPolynomial R) #[0] = #[] := by
  unfold CompPoly.CPolynomial.add;
  unfold CompPoly.CPolynomial.addRaw; simp +decide ;
  -- Since the array is empty, its last non-zero index is none, and thus the trimmed array is also empty.
  simp [CompPoly.CPolynomial.trim, CompPoly.CPolynomial.lastNonzero];
  simp +decide [ Array.findIdxRev? ];
  unfold Array.findIdxRev?.find; simp +decide ;
  unfold Array.findIdxRev?.find; simp +decide ;
  rfl

/-
Adding `#[]` and `#[0]` results in `#[]`.
-/
lemma add_empty_zero {R : Type*} [Ring R] [BEq R] [LawfulBEq R] : CompPoly.CPolynomial.add (#[] : CompPoly.CPolynomial R) #[0] = #[] := by
  convert add_zero_zero using 1;
  exact?

/-
Counterexample to strict distributivity. Uses `add_empty_zero`, `mul_empty`, `add_zero_zero`.
-/
open CompPoly CPolynomial

variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]

lemma mul_distrib_counterexample : mul #[] (#[] + (#[0] : CPolynomial R)) ≠ mul #[] #[] + mul #[] #[0] := by
  have h_add_empty_zero : CPolynomial.add (#[] : CPolynomial R) #[0] = #[] := by
    exact?;
  convert show ( #[0] : CPolynomial R ) ≠ #[] from ?_ using 1;
  exact ne_of_apply_ne Array.size ( by simp +decide )

end AristotleLemmas

theorem mul_distrib [LawfulBEq R] (p q r : CPolynomial R) : p * (q +r) = p * q + p * r := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  simp +zetaDelta at *;
  refine' ⟨ _, _, _, _, _ ⟩;
  exact ULift ℤ;
  exact inferInstance;
  exact inferInstance;
  · refine' { .. };
    simp +zetaDelta at *;
  · refine' ⟨ _, _, _, _ ⟩;
    exact #[];
    exact #[];
    exact #[0];
    native_decide +revert

-/
theorem mul_distrib [LawfulBEq R] (p q r : CPolynomial R) : p * (q +r) = p * q + p * r := by sorry

def zero : CPolynomial ℤ := CPolynomial.mk #[0]
def addid : CPolynomial ℤ := CPolynomial.mk #[]

#eval  addid * (addid + zero)-- this is #[1, 1]
#eval addid*addid + addid* zero--  returns false

def poly : CPolynomial (ZMod 6) := CPolynomial.mk #[2]
def qoly : CPolynomial (ZMod 6) := CPolynomial.mk #[3]

#eval poly * qoly
#eval qoly * poly

def ppoly : CPolynomial (ZMod 6) := CPolynomial.mk #[]
def qqoly : CPolynomial (ZMod 6) := CPolynomial.mk #[0]

#eval ppoly * qqoly
#eval qqoly * ppoly

def pppoly : CPolynomial (ZMod 6) := CPolynomial.mk #[1]
def qqqoly : CPolynomial (ZMod 6) := CPolynomial.mk #[1,1,1,1,0,0]

#eval pppoly * qqqoly
#eval qqqoly * pppoly

def roly : CPolynomial (ZMod 6) := CPolynomial.mk #[]
def soly : CPolynomial (ZMod 6) := CPolynomial.mk #[0]

#eval roly * soly
#eval soly * roly



end Operations

section AddCommSemigroup

/-- `CPolynomial R` forms a commutative semigroup under addition if R is a semiring.
-/
instance [LawfulBEq R] : AddCommSemigroup (CPolynomial R) where
  add_assoc := by intro _ _ _; rw [add_assoc]
  add_comm := add_comm

end AddCommSemigroup

section Monoid

/- Aristotle took a wrong turn (reason code: 13). Please try again. -/
/-- `CPolynomial R` forms a monoid under multiplication if R is a ring.
-/
instance [LawfulBEq R] : Monoid (CPolynomial R) where
  mul_assoc := by intro p q r; rw[mul_assoc]
  one_mul := sorry
  mul_one := sorry

end Monoid

section Monoid

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Type mismatch
  mul_comm
has type
  ∀ (a b : ?m.3), @HMul.hMul ?m.3 ?m.3 ?m.3 (@instHMul ?m.3 CommMagma.toMul) a b = b * a
but is expected to have type
  ∀ (a b : CompPoly.CPolynomial R),
    @HMul.hMul (CompPoly.CPolynomial R) (CompPoly.CPolynomial R) (CompPoly.CPolynomial R)
        (@instHMul (CompPoly.CPolynomial R) CompPoly.CPolynomial.instMonoidOfLawfulBEq.toMul) a b =
      b * a-/
/-- `CPolynomial R` forms a commutative monoid under multiplication if R is a commutative ring.
-/
instance [LawfulBEq R] [CommRing R] : CommMonoid (CPolynomial R) where
  mul_comm := mul_comm

end Monoid

end CPolynomial

end CompPoly
