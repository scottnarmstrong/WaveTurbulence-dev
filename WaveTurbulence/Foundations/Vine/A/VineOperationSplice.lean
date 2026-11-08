/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineOperationLayers
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceKernel
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

/-- Actual merge classes commute with every selected-family LF operation, including choice false. -/
theorem operation_splice_classes {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (b : GBranch A.skeleton.tree) :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).cls ((operationMolIso op).e b) =
      ((stSt A.skeleton σ).cls b).map (operationMolIso op).e :=
  operation_splice_classesMk hF op (Stage1Mk.markTransported_empty _) b

/-- B1b-2 (Mk-general form of `operationSpliceMolIso`). -/
noncomputable def operationSpliceMolIsoMk {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVine A.skeleton)} (hF : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk') :
    MolIso (stSt A.skeleton σ Mk).G.molecule
      (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk').G.molecule :=
  quotientMolIso (operationMolIso op) (operation_splice_classesMk hF op hT)
    (stSt A.skeleton σ Mk).M (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk').M

/-- Both choices of the actual operation induce an actual simultaneous-splice molecular map. -/
noncomputable def operationSpliceMolIso {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    MolIso (stSt A.skeleton σ).G.molecule
      (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).G.molecule :=
  operationSpliceMolIsoMk hF op (Stage1Mk.markTransported_empty _)

/-- B1b-2 (Mk-general form of `operationSpliceMolIso_branch_names`). -/
theorem operationSpliceMolIso_branch_namesMk {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVine A.skeleton)} (hF : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    (c : GBranch (stSt A.skeleton σ Mk).G.tree) :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk').M.ob
      ((operationSpliceMolIsoMk hF op hT).e c) = (operationMolIso op).e ((stSt A.skeleton σ Mk).M.ob c) :=
  quotientBranchEquiv_comm (operationMolIso op) (operation_splice_classesMk hF op hT) _ _ c

/-- The actual operation's splice atom map has the actual source branch names. -/
theorem operationSpliceMolIso_branch_names {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (c : GBranch (stSt A.skeleton σ).G.tree) :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).M.ob
      ((operationSpliceMolIso hF op).e c) = (operationMolIso op).e ((stSt A.skeleton σ).M.ob c) :=
  operationSpliceMolIso_branch_namesMk hF op (Stage1Mk.markTransported_empty _) c

end WaveTurbulence.VineA
