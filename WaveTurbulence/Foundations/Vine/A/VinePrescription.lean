/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineBatchIso
public import WaveTurbulence.Foundations.Stage1.Represents.RepSel
/-! VINE-A2: literal maximal-group and sigma transport along actual LF batches.
No compatibility of arbitrary per-garden choices is assumed. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Represents

variable {w : ℕ} {G H : Garden w}

/-- The maximal groups are canonically identified by an actual molecule isomorphism. -/
def groupEquiv (F : MolIso G.molecule H.molecule) :
    {S // S ∈ maximalGroups G.molecule} ≃ {T // T ∈ maximalGroups H.molecule} where
  toFun S := ⟨F.img S.1, F.maximalGroups_img S.2⟩
  invFun T := ⟨F.symm.img T.1, F.symm.maximalGroups_img T.2⟩
  left_inv S := Subtype.ext (F.img_img_symm S.1)
  right_inv T := Subtype.ext (F.img_symm_img T.1)

/-- Transport of the total S2a prescription by the atom bijection. -/
def transportPrescription (F : MolIso G.molecule H.molecule) (σ : Prescription G) : Prescription H :=
  fun T => σ (F.symm.img T)

theorem transportPrescription_apply (F : MolIso G.molecule H.molecule) (σ : Prescription G)
    (S : Finset (GBranch G.tree)) : transportPrescription F σ (F.img S) = σ S := by
  rw [transportPrescription, F.img_img_symm]

/-- Transport on the group's actual finite index type, as used by S2. -/
def transportGroupPrescription (F : MolIso G.molecule H.molecule) (σ : GroupPrescription G) :
    GroupPrescription H := fun T => σ ((groupEquiv F).symm T)

theorem transportGroupPrescription_apply (F : MolIso G.molecule H.molecule)
    (σ : GroupPrescription G) (S : {S // S ∈ maximalGroups G.molecule}) :
    transportGroupPrescription F σ (groupEquiv F S) = σ S :=
  congrArg σ ((groupEquiv F).symm_apply_apply S)

end WaveTurbulence.VineA
