/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescription
/-! VINE-A2: the source selected-vine carrier is equivariant under an actual
unit LF skeleton twist, with sigma transported on maximal atom groups. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w}

/-- Every selected source vine has a selected image, with exact geometric coordinates. -/
theorem vinesV0_image (Z : TwistGroupSite G) (σ : Prescription G) {c : CLVine G}
    (hc : c ∈ vinesV0 G σ) :
    ∃ c' ∈ vinesV0 Z.target (transportPrescription Z.iso σ),
      c'.atoms = Z.iso.img c.atoms ∧ c'.upper = Z.iso.e c.upper ∧ c'.lower = Z.iso.e c.lower := by
  obtain ⟨c', hc', ha, hu, hl⟩ := Z.vinesV_image hc.1
  obtain ⟨S, hS, hi, hs⟩ := hc.2
  refine ⟨c', ⟨hc', Z.iso.img S, Z.iso.maximalGroups_img hS, ?_, ?_⟩, ha, hu, hl⟩
  · rw [ha]
    exact Z.iso.isIngredient_img hi
  · rw [transportPrescription_apply]
    exact hs

/-- Every selected target vine comes from a selected source vine. -/
theorem vinesV0_preimage (Z : TwistGroupSite G) (σ : Prescription G) {c' : CLVine Z.target}
    (hc' : c' ∈ vinesV0 Z.target (transportPrescription Z.iso σ)) :
    ∃ c ∈ vinesV0 G σ,
      c'.atoms = Z.iso.img c.atoms ∧ c'.upper = Z.iso.e c.upper ∧ c'.lower = Z.iso.e c.lower := by
  obtain ⟨c, hc, ha, hu, hl⟩ := Z.vinesV_preimage hc'.1
  obtain ⟨S', hS', hi', hs'⟩ := hc'.2
  let S := Z.iso.symm.img S'
  have hS : S ∈ maximalGroups G.molecule := Z.iso.symm.maximalGroups_img hS'
  have hi : IsIngredient G.molecule S c.atoms := by
    apply Z.iso.isIngredient_img_iff.mp
    rw [show Z.iso.img S = S' from Z.iso.img_symm_img S']
    have ha' : Z.iso.img c.atoms = c'.atoms := ha
    rw [ha']
    exact hi'
  exact ⟨c, ⟨hc, S, hS, hi, hs'⟩, ha.symm, hu.symm, hl.symm⟩

/-- An actual bijection of the selected vine carriers (including non-core members). -/
noncomputable def selectedVineEquiv (Z : TwistGroupSite G) (σ : Prescription G) :
    {c : CLVine G // c ∈ vinesV0 G σ} ≃
      {c' : CLVine Z.target // c' ∈ vinesV0 Z.target (transportPrescription Z.iso σ)} := by
  let f : {c : CLVine G // c ∈ vinesV0 G σ} →
      {c' : CLVine Z.target // c' ∈ vinesV0 Z.target (transportPrescription Z.iso σ)} :=
    fun c => ⟨(vinesV0_image Z σ c.2).choose, (vinesV0_image Z σ c.2).choose_spec.1⟩
  apply Equiv.ofBijective f
  constructor
  · intro c d hcd
    have hc := (vinesV0_image Z σ c.2).choose_spec.2.1
    have hd := (vinesV0_image Z σ d.2).choose_spec.2.1
    have he : Z.iso.img c.1.atoms = Z.iso.img d.1.atoms :=
      hc.symm.trans ((congrArg (fun x => x.1.atoms) hcd).trans hd)
    exact Subtype.ext (clVine_eq_of_atoms (Z.iso.img_injective he))
  · intro c'
    obtain ⟨c, hc, ha, hu, hl⟩ := vinesV0_preimage Z σ c'.2
    refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    exact clVine_eq_of_atoms ((vinesV0_image Z σ hc).choose_spec.2.1.trans ha.symm)

end WaveTurbulence.VineA
