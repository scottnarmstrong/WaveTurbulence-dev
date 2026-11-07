/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw2Dec

/-! # K^T twist invariance, the local decoration bijection (V5 Step 4b, step 3, part 3)

`decEquiv`: `CLLocalDecoration R' L base ![e,f,g,h] ≃ CLLocalDecoration R L base ![f,e,g,h]`, `z' ↦ z' ∘ Θ` with `Θ` the
restriction of `twNode` to the supports (`support_iff`): the lower joint and the retained leaf exchange their labels, so the
first two boundary momenta are exchanged (TARGET `twistexplain` (d)).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} (P : CorePlacement G) {T : Finset (GBranch G.tree)} {z : GBranch G.tree}

/-- The branch bijection of the unit twist, typed in `(unitTwistGarden G P).tree`. -/
@[expose, reducible] noncomputable def eB : GBranch G.tree ≃ GBranch (unitTwistGarden G P).tree := coreBranchEquiv G P
/-- The leaf bijection of the unit twist, typed in `(unitTwistGarden G P).tree`. -/
@[expose, reducible] noncomputable def eL : GLeaf G.tree ≃ GLeaf (unitTwistGarden G P).tree := coreLeafEquiv G P

/-- Twisted region data, typed with `eB`. -/
@[expose] abbrev TwRegion (T : Finset (GBranch G.tree)) (z : GBranch G.tree) : Type :=
  CLRegionData (unitTwistGarden G P) (twistedAtoms G P T) (eB P P.lower) (eB P z)

variable (hB : G.molecule.IsBlock T P.lower z) (hCL : Mole.CLParentPattern G T P.lower z)
  (R : CLRegionData G T P.lower z) (R' : TwRegion P T z)

/-- The restriction of `twNode` to the supports. -/
@[expose] noncomputable def suppEquiv : ↥(clLocalSupport R) ≃ ↥(clLocalSupport R') :=
  Equiv.subtypeEquiv (twNode P) (support_iff P hB hCL R R')

include hB hCL in
theorem ext_comp {d : ℕ} (zz : ↥(clLocalSupport R') → (Fin d → ℤ)) (x : GNode G.tree) :
    clExtendIndices R (fun y => zz (suppEquiv P hB hCL R R' y)) x = clExtendIndices R' zz (twNode P x) := by
  classical
  by_cases hx : x ∈ clLocalSupport R
  · rw [clExtendIndices_apply R _ x hx, clExtendIndices_apply R' zz _ ((support_iff P hB hCL R R' x).mp hx)]
    rfl
  · have hx' : twNode P x ∉ clLocalSupport R' := fun h => hx ((support_iff P hB hCL R R' x).mpr h)
    unfold clExtendIndices
    rw [dif_neg hx, dif_neg hx']

include hB hCL R' in
theorem internal_iff (l : GLeaf G.tree) :
    Mole.IsInternalLeaf G T l ↔ Mole.IsInternalLeaf (unitTwistGarden G P) (twistedAtoms G P T) (eL P l) := by
  have hCL' := R'.parentPattern
  have h1 := real_iff P hB hCL hCL' l.toNode
  have e1 := Mole.leaf_incidence_realization_iff G T l
  have e2 := Mole.leaf_incidence_realization_iff (unitTwistGarden G P) (twistedAtoms G P T) (coreLeafEquiv G P l)
  have hn : naiveNodeEquiv G P l.toNode = (coreLeafEquiv G P l).toNode := naiveNodeEquiv_leaf G P l
  have e3 : Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P T) (naiveNodeEquiv G P l.toNode) ↔
      Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P T) (coreLeafEquiv G P l).toNode :=
    Iff.of_eq (congrArg (fun n : GNode (unitTwistGarden G P).tree =>
      Mole.InIncidenceRealization (unitTwistGarden G P) (twistedAtoms G P T) n) hn)
  exact e1.symm.trans (h1.trans (e3.trans e2))

include hB hCL in
theorem tw_bd (j : Fin 4) :
    twNode P (clBoundaryNodes R j) = clBoundaryNodes R' (Equiv.swap (0 : Fin 4) 1 j) := by
  obtain ⟨he, hk, hp, hn⟩ := region_eq P hB hCL R R'
  have hex : R.excluded = P.keep := excluded_eq_keep P hB R
  have hzl : z ≠ P.lower := by
    intro h
    have := (Mole.cl_parent_strict_descendant G hB hCL).2
    rw [h] at this
    exact lt_irrefl _ this
  fin_cases j
  · change twNode P P.lower.toNode = (eB P P.lower).child R'.excluded
    rw [he, hex]; exact twNode_lower P
  · change twNode P (P.lower.child R.excluded) = (eB P P.lower).toNode
    rw [hex]; exact twNode_lower_child_keep P
  · change twNode P (z.child R.positive) = (eB P z).child R'.positive
    rw [hp]; exact twNode_child P hB hCL hB.2.2.1 hzl _
  · change twNode P (z.child R.negative) = (eB P z).child R'.negative
    rw [hn]; exact twNode_child P hB hCL hB.2.2.1 hzl _

end WaveTurbulence.VineEstS4
