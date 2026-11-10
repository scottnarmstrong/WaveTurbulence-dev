/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.Vine.A.VineMarkTransport
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

/-- B1b (R11): `vinesV0_image` for a marked set carried by the twist (`MarkTransported`). -/
theorem vinesV0_imageMk (Z : TwistGroupSite G) (σ : Prescription G) {Mk : Set (CLVine G)}
    {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk') {c : CLVine G}
    (hc : c ∈ vinesV0 G σ Mk) :
    ∃ c' ∈ vinesV0 Z.target (transportPrescription Z.iso σ) Mk',
      c'.atoms = Z.iso.img c.atoms ∧ c'.upper = Z.iso.e c.upper ∧ c'.lower = Z.iso.e c.lower := by
  obtain ⟨hc0, hcM⟩ := mem_vinesV0.mp hc
  obtain ⟨c', hc', ha, hu, hl⟩ := vinesV0_image Z σ hc0
  exact ⟨c', mem_vinesV0.mpr ⟨hc', fun hm => hcM ((hT c c' ha).mpr hm)⟩, ha, hu, hl⟩

/-- B1b (R11): `vinesV0_preimage` for a marked set carried by the twist (`MarkTransported`). -/
theorem vinesV0_preimageMk (Z : TwistGroupSite G) (σ : Prescription G) {Mk : Set (CLVine G)}
    {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk') {c' : CLVine Z.target}
    (hc' : c' ∈ vinesV0 Z.target (transportPrescription Z.iso σ) Mk') :
    ∃ c ∈ vinesV0 G σ Mk,
      c'.atoms = Z.iso.img c.atoms ∧ c'.upper = Z.iso.e c.upper ∧ c'.lower = Z.iso.e c.lower := by
  obtain ⟨hc0, hcM⟩ := mem_vinesV0.mp hc'
  obtain ⟨c, hc, ha, hu, hl⟩ := vinesV0_preimage Z σ hc0
  exact ⟨c, mem_vinesV0.mpr ⟨hc, fun hm => hcM ((hT c c' ha).mp hm)⟩, ha, hu, hl⟩

end WaveTurbulence.VineA
