/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineFineOperation
/-! Actual selected-family, unit-list and b_sk transport along composed LF
batch traces. No isomorphism is chosen independently of the actual trace. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- Exact selected-family states are preserved through every actual batch trace. -/
theorem BatchIso.selected (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) : IsV0Fam B.family (transportPrescription F σ) := by
  induction h with
  | nil A => rw [transportPrescription_refl]; exact hA
  | skip _ _ ih => exact ih σ hA
  | @apply L A B i op J h ih =>
    have hb := ih (transportPrescription (operationMolIso op) σ) (isV0Fam_operation hA op)
    rw [transportPrescription_trans] at hb
    exact hb

/-- B1b (R11): the unmarked selected family transports through every actual batch trace, for marked sets carried by
the composite transport (`MarkTransported`; the intermediate marked sets are `Stage1Mk.midMark`). -/
theorem BatchIso.selectedMk (h : BatchIso p kind L A B F) :
    ∀ (σ : Prescription A.skeleton) (Mk : Set (Stage1.CLVine A.skeleton)) (Mk' : Set (Stage1.CLVine B.skeleton)),
      IsV0Fam A.family σ Mk → Stage1Mk.MarkTransported F Mk Mk' →
        IsV0Fam B.family (transportPrescription F σ) Mk' := by
  induction h with
  | nil A =>
    intro σ Mk Mk' hA hT
    rw [transportPrescription_refl, ← Stage1Mk.markTransported_refl_eq hT]
    exact hA
  | skip _ _ ih => exact ih
  | @apply L A B i op J h ih =>
    intro σ Mk Mk' hA hT
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) J hT
    have hb := ih (transportPrescription (operationMolIso op) σ) _ Mk' (isV0Fam_operationMk hA op h1) h2
    rw [transportPrescription_trans] at hb
    exact hb

/-- B1b-2 (Mk-general form of `BatchIso.units`): unit (run) lists transport through every batch trace, for marked
sets carried by the composite transport. -/
theorem BatchIso.unitsMk (h : BatchIso p kind L A B F) :
    ∀ (σ : Prescription A.skeleton) (Mk : Set (Stage1.CLVine A.skeleton)) (Mk' : Set (Stage1.CLVine B.skeleton)),
      IsV0Fam A.family σ Mk → Stage1Mk.MarkTransported F Mk Mk' →
      ((unitBlocks A.skeleton σ Mk).map (fun u => F.img u.atoms)).Perm
        ((unitBlocks B.skeleton (transportPrescription F σ) Mk').map CLBlock.atoms) := by
  induction h with
  | nil A =>
    intro σ Mk Mk' _ hT
    rw [transportPrescription_refl, ← Stage1Mk.markTransported_refl_eq hT]
    have he : (fun u : CLBlock A.skeleton => (molIsoRefl A.skeleton).img u.atoms) = CLBlock.atoms :=
      funext fun u => Finset.image_id
    rw [he]
  | skip _ _ ih => exact ih
  | @apply L A B i op J h ih =>
    intro σ Mk Mk' hA hT
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) J hT
    have hp := (operation_unitBlocks_permMk hA op h1).map J.img
    have hp' : ((unitBlocks A.skeleton σ Mk).map
        (fun u => (molIsoTrans (operationMolIso op) J).img u.atoms)).Perm
        ((unitBlocks op.output.skeleton (transportPrescription (operationMolIso op) σ)
          (Stage1Mk.midMark (operationMolIso op) J Mk Mk')).map (fun u => J.img u.atoms)) := by
      simpa only [List.map_map, Function.comp_def, molIsoTrans_img] using hp
    have hb := ih (transportPrescription (operationMolIso op) σ) _ Mk' (isV0Fam_operationMk hA op h1) h2
    rw [transportPrescription_trans] at hb
    exact hp'.trans hb

/-- Actual chosen unit lists transport through every actual batch trace. -/
theorem BatchIso.units (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) :
    ((unitBlocks A.skeleton σ).map (fun u => F.img u.atoms)).Perm
      ((unitBlocks B.skeleton (transportPrescription F σ)).map CLBlock.atoms) :=
  h.unitsMk σ ∅ ∅ hA (Stage1Mk.markTransported_empty F)

/-- B1b-2 (Mk-general form of `BatchIso.badCount`). -/
theorem BatchIso.badCountMk (h : BatchIso p kind L A B F) :
    ∀ (σ : Prescription A.skeleton) (Mk : Set (Stage1.CLVine A.skeleton)) (Mk' : Set (Stage1.CLVine B.skeleton)),
      IsV0Fam A.family σ Mk → Stage1Mk.MarkTransported F Mk Mk' →
      bskOf B.skeleton (transportPrescription F σ) Mk' = bskOf A.skeleton σ Mk := by
  induction h with
  | nil A =>
    intro σ Mk Mk' _ hT
    rw [transportPrescription_refl, ← Stage1Mk.markTransported_refl_eq hT]
  | skip _ _ ih => exact ih
  | @apply L A B i op J h ih =>
    intro σ Mk Mk' hA hT
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) J hT
    have hb := ih (transportPrescription (operationMolIso op) σ) _ Mk' (isV0Fam_operationMk hA op h1) h2
    rw [transportPrescription_trans] at hb
    exact hb.trans (bskOf_operationMk hA op h1)

/-- The actual b_sk count is invariant along every actual batch trace. -/
theorem BatchIso.badCount (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) : bskOf B.skeleton (transportPrescription F σ) = bskOf A.skeleton σ :=
  h.badCountMk σ ∅ ∅ hA (Stage1Mk.markTransported_empty F)

end WaveTurbulence.VineA
