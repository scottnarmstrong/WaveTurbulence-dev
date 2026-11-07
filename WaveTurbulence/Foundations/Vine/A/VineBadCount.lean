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

/-- The actual selected bad-ingredient sets correspond under the atom map. -/
theorem badUnitIngredients_image (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    Z.iso.img '' (unitIngredients G σ ∩ {T | IsBadVineSet G T}) =
      unitIngredients Z.target (transportPrescription Z.iso σ) ∩ {T | IsBadVineSet Z.target T} := by
  ext T'
  constructor
  · rintro ⟨T, ⟨hi, hb⟩, rfl⟩
    exact ⟨(unitIngredients_image_iff Z σ hsel T).mpr hi, (isBadVineSet_image_iff Z.iso T).mpr hb⟩
  · intro ht
    refine ⟨Z.iso.symm.img T', ⟨?_, ?_⟩, Z.iso.img_symm_img T'⟩
    · apply (unitIngredients_image_iff Z σ hsel _).mp
      rw [Z.iso.img_symm_img]
      exact ht.1
    · apply (isBadVineSet_image_iff Z.iso _).mp
      rw [Z.iso.img_symm_img]
      exact ht.2

/-- The actual b_sk count is invariant under a selected unit LF twist. -/
theorem bskOf_unitTwist (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    bskOf Z.target (transportPrescription Z.iso σ) = bskOf G σ := by
  change (unitIngredients Z.target (transportPrescription Z.iso σ) ∩
    {T | IsBadVineSet Z.target T}).ncard = (unitIngredients G σ ∩ {T | IsBadVineSet G T}).ncard
  rw [← badUnitIngredients_image Z σ hsel, Set.ncard_image_of_injective _ Z.iso.img_injective]

end WaveTurbulence.VineA
