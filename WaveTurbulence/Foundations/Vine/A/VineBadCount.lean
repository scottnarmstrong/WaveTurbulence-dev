/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitIngredients
/-! The bad-vine contribution b_sk is unchanged under a selected unit LF
twist, by transport of the actual unit-ingredient carrier and molecular type. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- B1b-2 (Mk-general form of `badUnitIngredients_image`). -/
theorem badUnitIngredients_imageMk (Z : TwistGroupSite G) (σ : Prescription G) {Mk : Set (CLVine G)}
    {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    Z.iso.img '' (unitIngredients G σ Mk ∩ {T | IsBadVineSet G T}) =
      unitIngredients Z.target (transportPrescription Z.iso σ) Mk' ∩ {T | IsBadVineSet Z.target T} := by
  ext T'
  constructor
  · rintro ⟨T, ⟨hi, hb⟩, rfl⟩
    exact ⟨(unitIngredients_image_iffMk Z σ hT hsel T).mpr hi, (isBadVineSet_image_iff Z.iso T).mpr hb⟩
  · intro ht
    refine ⟨Z.iso.symm.img T', ⟨?_, ?_⟩, Z.iso.img_symm_img T'⟩
    · apply (unitIngredients_image_iffMk Z σ hT hsel _).mp
      rw [Z.iso.img_symm_img]
      exact ht.1
    · apply (isBadVineSet_image_iff Z.iso _).mp
      rw [Z.iso.img_symm_img]
      exact ht.2

/-- The actual selected bad-ingredient sets correspond under the atom map. -/
theorem badUnitIngredients_image (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    Z.iso.img '' (unitIngredients G σ ∩ {T | IsBadVineSet G T}) =
      unitIngredients Z.target (transportPrescription Z.iso σ) ∩ {T | IsBadVineSet Z.target T} :=
  badUnitIngredients_imageMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel

/-- B1b-2 (Mk-general form of `bskOf_unitTwist`): `b_sk` at the marked sets is invariant under a selected unit twist
at an unmarked vine. -/
theorem bskOf_unitTwistMk (Z : TwistGroupSite G) (σ : Prescription G) {Mk : Set (CLVine G)}
    {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    bskOf Z.target (transportPrescription Z.iso σ) Mk' = bskOf G σ Mk := by
  change (unitIngredients Z.target (transportPrescription Z.iso σ) Mk' ∩
    {T | IsBadVineSet Z.target T}).ncard = (unitIngredients G σ Mk ∩ {T | IsBadVineSet G T}).ncard
  rw [← badUnitIngredients_imageMk Z σ hT hsel, Set.ncard_image_of_injective _ Z.iso.img_injective]

/-- The actual b_sk count is invariant under a selected unit LF twist. -/
theorem bskOf_unitTwist (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    bskOf Z.target (transportPrescription Z.iso σ) = bskOf G σ :=
  bskOf_unitTwistMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel

end WaveTurbulence.VineA
