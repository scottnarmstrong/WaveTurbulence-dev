/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.Vine.A.VineAllSiteIngredients
public import WaveTurbulence.Foundations.Vine.A.VineBatchFamily
/-! Actual unit and bad-count transport for coarse-family LF operations
at arbitrary prescriptions, retaining all exceptional reconstruction choices. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- Actual unit lists transport for every admissible operation and either choice. -/
theorem operation_coarse_units {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsVFamily A)
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
    · exact unitBlocks_atoms_perm (siteOfMember hF i) σ

/-- The actual b_sk contribution is preserved by every admissible LF operation. -/
theorem bskOf_coarse_operation {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsVFamily A)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    bskOf op.output.skeleton (transportPrescription (operationMolIso op) σ) = bskOf A.skeleton σ := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · exact congrArg (bskOf A.skeleton) (transportPrescription_refl σ)
    · exact bskOf_unitTwist_allSites (siteOfMember hF i) σ

end WaveTurbulence.VineA
