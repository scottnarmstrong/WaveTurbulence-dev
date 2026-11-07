/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineCoarseOperation
/-! Actual unit-list and bad-count transport along coarse LF batches
for arbitrary prescriptions and both canonical object kinds. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- Actual chosen unit lists transport through every actual batch trace. -/
theorem BatchIso.coarseUnits (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsVFamily A) :
    ((unitBlocks A.skeleton σ).map (fun u => F.img u.atoms)).Perm
      ((unitBlocks B.skeleton (transportPrescription F σ)).map CLBlock.atoms) := by
  induction h with
  | nil A =>
    rw [transportPrescription_refl]
    have he : (fun u : CLBlock A.skeleton => (molIsoRefl A.skeleton).img u.atoms) = CLBlock.atoms :=
      funext fun u => Finset.image_id
    rw [he]
  | skip _ _ ih => exact ih σ hA
  | @apply L A B i op J h ih =>
    have hp := (operation_coarse_units (σ := σ) hA op).map J.img
    have hp' : ((unitBlocks A.skeleton σ).map (fun u => (molIsoTrans (operationMolIso op) J).img u.atoms)).Perm
        ((unitBlocks op.output.skeleton (transportPrescription (operationMolIso op) σ)).map (fun u => J.img u.atoms)) := by
      simpa only [List.map_map, Function.comp_def, molIsoTrans_img] using hp
    have hb := ih (transportPrescription (operationMolIso op) σ) (isVFamily_output hA op)
    rw [transportPrescription_trans] at hb
    exact hp'.trans hb

/-- The actual b_sk count is invariant along every actual batch trace. -/
theorem BatchIso.coarseBadCount (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsVFamily A) : bskOf B.skeleton (transportPrescription F σ) = bskOf A.skeleton σ := by
  induction h with
  | nil A => rw [transportPrescription_refl]
  | skip _ _ ih => exact ih σ hA
  | @apply L A B i op J h ih =>
    have hb := ih (transportPrescription (operationMolIso op) σ) (isVFamily_output hA op)
    rw [transportPrescription_trans] at hb
    exact hb.trans (bskOf_coarse_operation (σ := σ) hA op)

end WaveTurbulence.VineA
