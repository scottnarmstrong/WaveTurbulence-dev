/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.Vine.A.VineBadCount
public import WaveTurbulence.Foundations.Vine.A.VineBatchFamily
/-! Exact selected-family and actual unit transport for both choices of an
admissible LF operation. All exceptional reconstruction choices are retained. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- Identity transport preserves the total prescription. -/
theorem transportPrescription_refl {G : Garden w} (σ : Prescription G) :
    transportPrescription (molIsoRefl G) σ = σ := by
  funext T
  change σ (T.image id) = σ T
  rw [Finset.image_id]

/-- Prescription transport composes along the actual atom maps. -/
theorem transportPrescription_trans {G H K : Garden w} (F : MolIso G.molecule H.molecule)
    (J : MolIso H.molecule K.molecule) (σ : Prescription G) :
    transportPrescription J (transportPrescription F σ) = transportPrescription (molIsoTrans F J) σ := by
  funext T
  change σ ((T.image J.e.symm).image F.e.symm) = σ (T.image (F.e.symm ∘ J.e.symm))
  rw [Finset.image_image]

/-- Both choices of an actual operation preserve exact selected-family states. -/
theorem isV0Fam_operation {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    IsV0Fam op.output.family (transportPrescription (operationMolIso op) σ) := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · change IsV0Fam A.family (transportPrescription (molIsoRefl A.skeleton) σ)
      rw [transportPrescription_refl]
      exact hF
    · exact isV0Fam_twist hF i

/-- B1b (R11): both choices of an actual operation preserve exact unmarked selected-family states, for marked sets
carried by the operation. -/
theorem isV0Fam_operationMk {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVine A.skeleton)} (hF : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i) {Mk' : Set (CLVine op.output.skeleton)}
    (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk') :
    IsV0Fam op.output.family (transportPrescription (operationMolIso op) σ) Mk' := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · have hE : Mk = Mk' := Stage1Mk.markTransported_refl_eq hT
      change IsV0Fam A.family (transportPrescription (molIsoRefl A.skeleton) σ) Mk'
      rw [transportPrescription_refl]
      exact hE ▸ hF
    · exact isV0Fam_twistMk hF i hT

/-- Actual unit lists transport for every admissible operation and either choice. -/
theorem operation_unitBlocks_perm {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    ((unitBlocks A.skeleton σ).map (fun u => (operationMolIso op).img u.atoms)).Perm
      ((unitBlocks op.output.skeleton (transportPrescription (operationMolIso op) σ)).map CLBlock.atoms) := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · change ((unitBlocks A.skeleton σ).map (fun u => (molIsoRefl A.skeleton).img u.atoms)).Perm
        ((unitBlocks A.skeleton (transportPrescription (molIsoRefl A.skeleton) σ)).map CLBlock.atoms)
      rw [transportPrescription_refl]
      have he : (fun u : CLBlock A.skeleton => (molIsoRefl A.skeleton).img u.atoms) = CLBlock.atoms :=
        funext fun u => Finset.image_id
      rw [he]
    · exact unitBlocks_image_perm (selectedMemberSite hF i) σ ⟨familyVine A.family i, hF.1 i, rfl⟩

/-- The actual b_sk contribution is preserved by every admissible LF operation. -/
theorem bskOf_operation {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    bskOf op.output.skeleton (transportPrescription (operationMolIso op) σ) = bskOf A.skeleton σ := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · exact congrArg (bskOf A.skeleton) (transportPrescription_refl σ)
    · exact bskOf_unitTwist (selectedMemberSite hF i) σ ⟨familyVine A.family i, hF.1 i, rfl⟩

end WaveTurbulence.VineA
