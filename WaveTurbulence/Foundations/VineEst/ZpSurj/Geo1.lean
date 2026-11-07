/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Construct6
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.ZpSurjStmt

/-! # ZP-SURJ: the parent-layer numbers of a state -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5B WaveTurbulence.Mole

variable {w : ℕ} {ι : Type*}

/-- The parent-core layer of the partner of the retained leaf of the member `i`. -/
@[expose] noncomputable def numR (G : FamilyReconstruction w ι) (i : ι) : ℕ :=
  parentCoreLayer G.data G.plain (stateLayer G) (G.skeleton.pair (G.family.placement i).retained).toNode

theorem parentCore_retained (G : FamilyReconstruction w ι) (i : ι) :
    parentCoreLayer G.data G.plain (stateLayer G) (G.family.placement i).retained.toNode =
      (zpBranchQ G i).2 := by
  have hc := (G.family.placement i).child
  have hn : (G.family.placement i).retained.toNode.1.2 ≠ [] := by
    rw [hc]; simp [GBranch.child]
  unfold parentCoreLayer
  rw [dif_neg hn]
  have hp : (G.family.placement i).retained.toNode.parent hn = (G.family.placement i).lower :=
    Twist.parent_eq_of_child hn hc
  rw [hp]
  rfl

theorem retained_sign (G : FamilyReconstruction w ι) (i : ι) :
    nodeSign G.skeleton.sig (G.family.placement i).retained.1 = nuOf G i := by
  have hc := (G.family.placement i).child
  have h1 := child_sign_formula (G := G.skeleton) (G.family.placement i).lower (G.family.placement i).keep
  rw [if_neg (G.family.placement i).outer] at h1
  have h2 : G.skeleton.sign (G.family.placement i).retained.toNode = nodeSign G.skeleton.sig (G.family.placement i).retained.1 := rfl
  rw [hc] at h2
  rw [← h2, h1]
  rfl

open Classical in
theorem zpQQ_eq (G : FamilyReconstruction w ι) (i : ι) :
    zpQQ G i = (numR G i, (zpBranchQ G i).2) := by
  have hsg := retained_sign G i
  have hr := parentCore_retained G i
  unfold zpQQ zpPairQ pairQ
  by_cases hv : nuOf G i = -1
  · have hs : nodeSign G.skeleton.sig (G.family.placement i).retained.1 ≠ 1 := by
      rw [hsg, hv]; decide
    obtain ⟨h1, h2⟩ := pairOfLeaf_sides_neg G.skeleton G.plain _ hs
    rw [if_pos hv, h1, h2, hr]
    rfl
  · have hv1 : nuOf G i = 1 := by
      rcases Int.units_eq_one_or (nuOf G i) with h | h
      · exact h
      · exact absurd h hv
    have hs : nodeSign G.skeleton.sig (G.family.placement i).retained.1 = 1 := by rw [hsg, hv1]
    obtain ⟨h1, h2⟩ := pairOfLeaf_sides_pos G.skeleton G.plain _ hs
    rw [if_neg hv, h1, h2, hr]
    rfl

end WaveTurbulence.ZpSurj
