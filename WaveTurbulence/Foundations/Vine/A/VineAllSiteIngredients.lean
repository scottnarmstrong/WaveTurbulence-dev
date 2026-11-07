/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitAtoms
public import WaveTurbulence.Foundations.Vine.A.VineBadCount
/-! The actual unit-ingredient carrier and bad count transport at every
unit twist site, for arbitrary prescriptions. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- Arbitrary-prescription unit ingredients follow the actual atom bijection. -/
theorem unitIngredients_image_iff_allSites (Z : TwistGroupSite G) (σ : Prescription G)
    (T : Finset (GBranch G.tree)) :
    Z.iso.img T ∈ unitIngredients Z.target (transportPrescription Z.iso σ) ↔ T ∈ unitIngredients G σ := by
  constructor
  · rintro ⟨v, hv, x, y, n, p, q, hi⟩
    obtain ⟨u, hu, hat⟩ := unitBlocks_preimage_atoms Z σ hv
    have hi' := Z.iso.symm.chainIngredient_img hi
    rw [hat, Z.iso.img_img_symm, Z.iso.img_img_symm] at hi'
    exact ⟨u, hu, Z.iso.symm.e x, Z.iso.symm.e y, n, Z.iso.symm.e p, Z.iso.symm.e q, hi'⟩
  · rintro ⟨u, hu, x, y, n, p, q, hi⟩
    obtain ⟨v, hv, hat⟩ := unitBlocks_image_atoms Z σ hu
    refine ⟨v, hv, Z.iso.e x, Z.iso.e y, n, Z.iso.e p, Z.iso.e q, ?_⟩
    rw [hat]
    exact Z.iso.chainIngredient_img hi

/-- The actual bad-ingredient sets transport for every prescription. -/
theorem badUnitIngredients_image_allSites (Z : TwistGroupSite G) (σ : Prescription G) :
    Z.iso.img '' (unitIngredients G σ ∩ {T | IsBadVineSet G T}) =
      unitIngredients Z.target (transportPrescription Z.iso σ) ∩ {T | IsBadVineSet Z.target T} := by
  ext T'
  constructor
  · rintro ⟨T, ⟨hi, hb⟩, rfl⟩
    exact ⟨(unitIngredients_image_iff_allSites Z σ T).mpr hi, (isBadVineSet_image_iff Z.iso T).mpr hb⟩
  · intro ht
    refine ⟨Z.iso.symm.img T', ⟨?_, ?_⟩, Z.iso.img_symm_img T'⟩
    · apply (unitIngredients_image_iff_allSites Z σ _).mp
      rw [Z.iso.img_symm_img]
      exact ht.1
    · apply (isBadVineSet_image_iff Z.iso _).mp
      rw [Z.iso.img_symm_img]
      exact ht.2

/-- The actual bad count is invariant at every site and arbitrary prescription. -/
theorem bskOf_unitTwist_allSites (Z : TwistGroupSite G) (σ : Prescription G) :
    bskOf Z.target (transportPrescription Z.iso σ) = bskOf G σ := by
  change (unitIngredients Z.target (transportPrescription Z.iso σ) ∩
    {T | IsBadVineSet Z.target T}).ncard = (unitIngredients G σ ∩ {T | IsBadVineSet G T}).ncard
  rw [← badUnitIngredients_image_allSites Z σ, Set.ncard_image_of_injective _ Z.iso.img_injective]

end WaveTurbulence.VineA
