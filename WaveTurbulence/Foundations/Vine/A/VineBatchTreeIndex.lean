/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineBatchUnitJoints
public import WaveTurbulence.Foundations.Molecule.LFTwist.SameTree
/-! S2 consumer R-IDX: every actual LF trace preserves the original tree index
of every branch, in particular the upper joint of each transported actual unit. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LFTwist Twist
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- Source CL geometry forces each operation to act inside a single original tree. -/
theorem operationMolIso_tree_index {i : ι} (op : FamilyOperation (p := p) (kind := kind) A i)
    (b : GBranch A.skeleton.tree) : ((operationMolIso op).e b).1.1 = b.1.1 := by
  change ((chosenMolIso A.skeleton (A.family.placement i) op.choice).e b).1.1 = b.1.1
  cases hc : op.choice
  · rfl
  · exact coreBranchEquiv_tree_index (A.family.placement i)
      (placement_same_tree (A.family.placement i) (A.family.core i).1.1
        (A.family.core i).2.1 (A.family.designated i)) b

/-- Every branch keeps its source tree index along the literal composed batch map. -/
theorem BatchIso.tree_index (h : BatchIso p kind L A B F) (b : GBranch A.skeleton.tree) :
    (F.e b).1.1 = b.1.1 := by
  induction h with
  | nil A => rfl
  | skip _ _ ih => exact ih b
  | @apply L A B i op J h ih =>
    exact (ih ((operationMolIso op).e b)).trans (operationMolIso_tree_index op b)

/-- The actual matching target unit has the source unit's upper-joint tree index (R-IDX). -/
theorem BatchIso.unit_upper_tree_index (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) (u : CLBlock A.skeleton)
    (hu : u ∈ unitBlocks A.skeleton σ) :
    ∃ v ∈ unitBlocks B.skeleton (transportPrescription F σ),
      v.atoms = F.img u.atoms ∧ v.upper = F.e u.upper ∧ v.lower = F.e u.lower ∧
        v.upper.1.1 = u.upper.1.1 := by
  obtain ⟨v, hv, ha, htop, hbottom⟩ := h.units_joints σ hA hu
  exact ⟨v, hv, ha, htop, hbottom, (congrArg (fun b => b.1.1) htop).trans (h.tree_index u.upper)⟩

end WaveTurbulence.VineA
