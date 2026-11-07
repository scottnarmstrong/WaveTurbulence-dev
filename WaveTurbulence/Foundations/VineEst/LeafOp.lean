/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VineEst.LeafCorr3

/-! # The leaf correspondence of one family operation (LFTWIST-LEAFMAP, step 5)

Statements on the leaves `GLeaf A.layered.garden.tree` of the layered gardens of the states. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LFTwist
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree Links
variable {w p : ℕ} {kind : Bool} {ι : Type*}

theorem FamilyReconstruction.garden_eq (A : FamilyReconstruction w ι) :
    A.layered.garden = A.data.garden A.plain :=
  rawOfGarden_injective_plain A.decodes.1 (A.data.garden_plain A.plain)
    (A.decodes.2.symm.trans (A.data.garden_raw A.plain).symm)

theorem FamilyReconstruction.sig_eq (A : FamilyReconstruction w ι) : A.layered.garden.sig = A.skeleton.sig :=
  (congrArg Raw.sig A.decodes.2).symm

/-- A leaf of the layered garden, seen as a leaf of the decoded forest. -/
@[expose] def FamilyReconstruction.dataLeaf (A : FamilyReconstruction w ι) (x : GLeaf A.layered.garden.tree) :
    GLeaf (A.data.forest A.plain) :=
  ⟨x.1, (congrArg (fun G : Garden w => x.1.2 ∈ (G.tree x.1.1).leaves) A.garden_eq).mp x.2⟩

theorem FamilyReconstruction.dataLeaf_val (A : FamilyReconstruction w ι) (x : GLeaf A.layered.garden.tree) :
    (A.dataLeaf x).1 = x.1 := rfl

/-- Leaves of the layered garden corresponding to a decoded-forest leaf. -/
@[expose] def FamilyReconstruction.gardenLeaf (A : FamilyReconstruction w ι) (x : GLeaf (A.data.forest A.plain)) :
    GLeaf A.layered.garden.tree :=
  ⟨x.1, (congrArg (fun G : Garden w => x.1.2 ∈ (G.tree x.1.1).leaves) A.garden_eq).mpr x.2⟩

theorem FamilyReconstruction.pair_val (A : FamilyReconstruction w ι) (x : GLeaf A.layered.garden.tree) :
    (A.layered.garden.pair x).1 = ((A.data.garden A.plain).pair (A.dataLeaf x)).1 :=
  pair_val_congr A.garden_eq x (A.dataLeaf x) rfl

end WaveTurbulence.LFTwist
