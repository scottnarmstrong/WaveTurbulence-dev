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

/-- Actual merge classes commute with every selected-family LF operation, including choice false. -/
theorem operation_splice_classes {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (b : GBranch A.skeleton.tree) :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).cls ((operationMolIso op).e b) =
      ((stSt A.skeleton σ).cls b).map (operationMolIso op).e := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · change (stSt A.skeleton (transportPrescription (molIsoRefl A.skeleton) σ)).cls b =
        ((stSt A.skeleton σ).cls b).map id
      rw [transportPrescription_refl]
      cases (stSt A.skeleton σ).cls b <;> rfl
    · exact unitBlocks_cls_twist (selectedMemberSite hF i) σ ⟨familyVine A.family i, hF.1 i, rfl⟩ b

/-- Both choices of the actual operation induce an actual simultaneous-splice molecular map. -/
noncomputable def operationSpliceMolIso {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    MolIso (stSt A.skeleton σ).G.molecule
      (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).G.molecule :=
  quotientMolIso (operationMolIso op) (operation_splice_classes hF op)
    (stSt A.skeleton σ).M (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).M

/-- The actual operation's splice atom map has the actual source branch names. -/
theorem operationSpliceMolIso_branch_names {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (c : GBranch (stSt A.skeleton σ).G.tree) :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).M.ob
      ((operationSpliceMolIso hF op).e c) = (operationMolIso op).e ((stSt A.skeleton σ).M.ob c) :=
  quotientBranchEquiv_comm (operationMolIso op) (operation_splice_classes hF op) _ _ c

end WaveTurbulence.VineA
