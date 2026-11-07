/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInternalLeaves

/-! # Boundary nodes are exterior to the completely paired realization -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clBoundaryNode_not_internalLeaf (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (j : Fin 4) (ℓ : GLeaf G.tree) (he : clBoundaryNodes R j = ℓ.toNode) :
    ¬ Mole.IsInternalLeaf G U ℓ := by
  intro hl
  have hr := (cl_realization_iff hU R ℓ.toNode).mp
    ((Mole.leaf_incidence_realization_iff G U ℓ).mpr hl)
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj with rfl | rfl | rfl | rfl
  · exact Mole.branch_toNode_ne_leaf a ℓ he
  · apply hr.2.1
    change a.child R.excluded = ℓ.toNode at he
    rw [he]
    exact GNode.isDesc_refl _
  · apply hr.2.2.1
    change b.child R.positive = ℓ.toNode at he
    rw [he]
    exact GNode.isDesc_refl _
  · apply hr.2.2.2
    change b.child R.negative = ℓ.toNode at he
    rw [he]
    exact GNode.isDesc_refl _

end WaveTurbulence.VineEstS2
