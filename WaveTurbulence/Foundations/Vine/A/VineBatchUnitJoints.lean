/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineDesignatedSupport
public import WaveTurbulence.Foundations.Vine.A.VineCollectionGeometry
/-! Actual selected batches transport the full ordered CL unit joints. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- B1b-2 (Mk-general form of `operation_units_joints`). -/
theorem operation_units_jointsMk {A : FamilyReconstruction w ι} {i : ι} {σ : Prescription A.skeleton}
    {Mk : Set (CLVine A.skeleton)} (hA : IsV0Fam A.family σ Mk) (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    {u : CLBlock A.skeleton} (hu : u ∈ unitBlocks A.skeleton σ Mk) :
    ∃ v ∈ unitBlocks op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk',
      v.atoms = (operationMolIso op).img u.atoms ∧ v.upper = (operationMolIso op).e u.upper ∧
        v.lower = (operationMolIso op).e u.lower := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · obtain rfl : Mk = Mk' := Stage1Mk.markTransported_refl_eq hT
      change ∃ v ∈ unitBlocks A.skeleton (transportPrescription (molIsoRefl A.skeleton) σ) Mk,
        v.atoms = (molIsoRefl A.skeleton).img u.atoms ∧ v.upper = u.upper ∧ v.lower = u.lower
      rw [transportPrescription_refl]
      exact ⟨u, hu, Finset.image_id.symm, rfl, rfl⟩
    · let Z := selectedMemberSite hA i
      have hs : ∃ c ∈ vinesV0 A.skeleton σ Mk, c.atoms = Z.S0 := ⟨familyVine A.family i, hA.1 i, rfl⟩
      exact ⟨unitImage Z u (unitBlocks_goodMk Z σ hs hu), unitImage_memMk Z σ hT hs hu, rfl, rfl, rfl⟩

/-- B1b-2 (Mk-general form of `BatchIso.units_joints`). -/
theorem BatchIso.units_jointsMk {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk)
    {u : CLBlock A.skeleton} (hu : u ∈ unitBlocks A.skeleton σ Mk) :
    ∃ v ∈ unitBlocks B.skeleton (transportPrescription F σ) Mk',
      v.atoms = F.img u.atoms ∧ v.upper = F.e u.upper ∧ v.lower = F.e u.lower := by
  induction h with
  | nil A =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    rw [transportPrescription_refl]
    exact ⟨u, hu, Finset.image_id.symm, rfl, rfl⟩
  | skip _ _ ih => exact ih σ hT hA hu
  | @apply L A B i op J h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) J hT
    obtain ⟨v, hv, hva, hvu, hvl⟩ := operation_units_jointsMk hA op h1 hu
    obtain ⟨t, ht, hta, htu, htl⟩ := ih (transportPrescription (operationMolIso op) σ) h2
      (isV0Fam_operationMk hA op h1) hv
    rw [transportPrescription_trans] at ht
    refine ⟨t, ht, ?_, ?_, ?_⟩
    · exact hta.trans ((congrArg J.img hva).trans (molIsoTrans_img (operationMolIso op) J u.atoms).symm)
    · change t.upper = J.e ((operationMolIso op).e u.upper)
      exact htu.trans (congrArg J.e hvu)
    · change t.lower = J.e ((operationMolIso op).e u.lower)
      exact htl.trans (congrArg J.e hvl)

end WaveTurbulence.VineA
