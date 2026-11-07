/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineHingeGapChoice
/-! Actual selected batches transport the full ordered CL unit joints. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- Both LF choices transport actual unit supports and both ordered joints. -/
theorem operation_units_joints {A : FamilyReconstruction w ι} {i : ι} {σ : Prescription A.skeleton}
    (hA : IsV0Fam A.family σ) (op : FamilyOperation (p := p) (kind := kind) A i)
    {u : CLBlock A.skeleton} (hu : u ∈ unitBlocks A.skeleton σ) :
    ∃ v ∈ unitBlocks op.output.skeleton (transportPrescription (operationMolIso op) σ),
      v.atoms = (operationMolIso op).img u.atoms ∧ v.upper = (operationMolIso op).e u.upper ∧
        v.lower = (operationMolIso op).e u.lower := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · change ∃ v ∈ unitBlocks A.skeleton (transportPrescription (molIsoRefl A.skeleton) σ),
        v.atoms = (molIsoRefl A.skeleton).img u.atoms ∧ v.upper = u.upper ∧ v.lower = u.lower
      rw [transportPrescription_refl]
      exact ⟨u, hu, Finset.image_id.symm, rfl, rfl⟩
    · let Z := selectedMemberSite hA i
      have hs : ∃ c ∈ vinesV0 A.skeleton σ, c.atoms = Z.S0 := ⟨familyVine A.family i, hA.1 i, rfl⟩
      exact ⟨unitImage Z u (unitBlocks_good Z σ hs hu), unitImage_mem Z σ hs hu, rfl, rfl, rfl⟩

/-- Actual complete batch traces transport the full ordered CL units. -/
theorem BatchIso.units_joints {L : List ι} {A B : FamilyReconstruction w ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    {u : CLBlock A.skeleton} (hu : u ∈ unitBlocks A.skeleton σ) :
    ∃ v ∈ unitBlocks B.skeleton (transportPrescription F σ),
      v.atoms = F.img u.atoms ∧ v.upper = F.e u.upper ∧ v.lower = F.e u.lower := by
  induction h with
  | nil A =>
    rw [transportPrescription_refl]
    exact ⟨u, hu, Finset.image_id.symm, rfl, rfl⟩
  | skip _ _ ih => exact ih σ hA hu
  | @apply L A B i op J h ih =>
    obtain ⟨v, hv, hva, hvu, hvl⟩ := operation_units_joints hA op hu
    obtain ⟨t, ht, hta, htu, htl⟩ := ih (transportPrescription (operationMolIso op) σ)
      (isV0Fam_operation hA op) hv
    rw [transportPrescription_trans] at ht
    refine ⟨t, ht, ?_, ?_, ?_⟩
    · exact hta.trans ((congrArg J.img hva).trans (molIsoTrans_img (operationMolIso op) J u.atoms).symm)
    · change t.upper = J.e ((operationMolIso op).e u.upper)
      exact htu.trans (congrArg J.e hvu)
    · change t.lower = J.e ((operationMolIso op).e u.lower)
      exact htl.trans (congrArg J.e hvl)

end WaveTurbulence.VineA
