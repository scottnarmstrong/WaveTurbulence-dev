/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Cls4Ext

/-! # Class combinatorics, part 4: the states reached by one operation at `i` are determined by `sigStar _ i` (V5 Step 4b, WP-A)

`zp_eq_of_sigStar`: two states of `Zp(A)` (the start state `A` itself, or the output of an operation at the member `i`) with equal
signature at `i` are equal (prime start state).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool}

theorem sign_chosen (G : Garden w) (P : CorePlacement G) (ε : Bool) (b : GBranch G.tree) (hb : b ≠ P.lower) :
    nodeSign (chosenSkeleton G P ε).sig (chosenBranchEquiv G P ε b).1 = nodeSign G.sig b.1 := by
  cases ε
  · rfl
  · exact (coreBranchEquiv_sign G P b).trans (if_neg hb)

section Op
variable (A : FamilyReconstruction w ι) (i : ι)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement i) (A.family.kind i)
    (A.family.atoms i) (A.family.upper i))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement i).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement i).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement i).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement i).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement i).retained).secondLeaf A.plain).toNode)))

/-- The output of an operation at `i` agrees with the source on the ordinary rows. -/
@[expose] noncomputable def compat_op {ε : Bool} (con : LFConstruction (A.source i hcan hel htc hcc) ε) :
    Compat p A i (FamilyOperation.output (⟨hcan, hel, htc, hcc, ε, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).plain
      (chosenBranchEquiv A.skeleton (A.family.placement i) ε)
      (chosenPairEquiv A.skeleton (A.family.placement i) A.plain ε)
      (FamilyOperation.output (⟨hcan, hel, htc, hcc, ε, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).data
      (FamilyOperation.output (⟨hcan, hel, htc, hcc, ε, con⟩ : FamilyOperation (p := p) (kind := kind) A i)).layered where
  layer := stateLayer (FamilyOperation.output (⟨hcan, hel, htc, hcc, ε, con⟩ : FamilyOperation (p := p) (kind := kind) A i))
  hlay := stateLayer_isLayering _
  spec := stateLayer_spec _
  decodes := con.decodes
  crit := con.canonical.criterion
  sign_other := fun b hb => sign_chosen A.skeleton (A.family.placement i) ε b hb
  tree_other := fun b hb => con.tree_other b hb
  couple_other := fun q hq => con.couple_other q hq
  core := fun b => con.coreLayers b
  treeL := fun b hb q hq => con.ordinaryTreeLayers b hb q hq
  coupleL := fun q hq j r hr => con.ordinaryCoupleLayers q hq j r hr

end Op

/-- The state itself agrees with itself on the ordinary rows (as the FALSE choice at `i` with no change). -/
@[expose] noncomputable def compat_self (A : FamilyReconstruction w ι) (i : ι) (hcan : CanonicalObject p kind A.layered) :
    Compat p A i (chosenSkeleton_plain A.skeleton (A.family.placement i) A.plain false)
      (chosenBranchEquiv A.skeleton (A.family.placement i) false)
      (chosenPairEquiv A.skeleton (A.family.placement i) A.plain false) A.data A.layered where
  layer := stateLayer A
  hlay := stateLayer_isLayering A
  spec := stateLayer_spec A
  decodes := A.decodes
  crit := hcan.criterion
  sign_other := fun b _ => rfl
  tree_other := fun b _ => rfl
  couple_other := fun q _ => congrArg A.data.couple (pairOfLeaf_firstLeaf A.skeleton A.plain q)
  core := fun b => rfl
  treeL := fun b _ q _ => rfl
  coupleL := fun q _ j r _ => by
    have hq : chosenPairEquiv A.skeleton (A.family.placement i) A.plain false q = q :=
      pairOfLeaf_firstLeaf A.skeleton A.plain q
    rw [hq]
    rfl

end WaveTurbulence.VineEstS4
