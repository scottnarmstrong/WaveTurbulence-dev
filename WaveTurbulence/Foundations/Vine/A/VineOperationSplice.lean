/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineOperationLayers
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceDarts
/-! The actual splice quotient map for both choices of every admissible
selected-family LF operation, with exact original-branch names. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- B1b-2 (Mk-general form of `operation_splice_classes`). -/
theorem operation_splice_classesMk {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVine A.skeleton)} (hF : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    (b : GBranch A.skeleton.tree) :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk').cls ((operationMolIso op).e b) =
      ((stSt A.skeleton σ Mk).cls b).map (operationMolIso op).e := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · obtain rfl : Mk = Mk' := Stage1Mk.markTransported_refl_eq hT
      change (stSt A.skeleton (transportPrescription (molIsoRefl A.skeleton) σ) Mk).cls b =
        ((stSt A.skeleton σ Mk).cls b).map id
      rw [transportPrescription_refl]
      cases (stSt A.skeleton σ Mk).cls b <;> rfl
    · exact unitBlocks_cls_twistMk (selectedMemberSite hF i) σ hT ⟨familyVine A.family i, hF.1 i, rfl⟩ b

end WaveTurbulence.VineA
