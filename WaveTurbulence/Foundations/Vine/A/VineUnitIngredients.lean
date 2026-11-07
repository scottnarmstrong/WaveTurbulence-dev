/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitList
public import WaveTurbulence.Foundations.FinalCount.RedSpliceData
/-! The actual unit-ingredient carrier and its bad-vine predicate transport
under a selected unit LF twist. These use the chosen unitBlocks lists. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- Actual ingredients of the chosen units transport in both directions. -/
theorem unitIngredients_image_iff (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (T : Finset (GBranch G.tree)) :
    Z.iso.img T ∈ unitIngredients Z.target (transportPrescription Z.iso σ) ↔ T ∈ unitIngredients G σ := by
  constructor
  · rintro ⟨v, hv, x, y, n, p, q, hi⟩
    obtain ⟨u, hu, hat, _, _⟩ := unitBlocks_preimage Z σ hsel hv
    have hi' := Z.iso.symm.chainIngredient_img hi
    rw [hat, Z.iso.img_img_symm, Z.iso.img_img_symm] at hi'
    exact ⟨u, hu, Z.iso.symm.e x, Z.iso.symm.e y, n, Z.iso.symm.e p, Z.iso.symm.e q, hi'⟩
  · rintro ⟨u, hu, x, y, n, p, q, hi⟩
    exact ⟨unitImage Z u (unitBlocks_good Z σ hsel hu), unitImage_mem Z σ hsel hu,
      Z.iso.e x, Z.iso.e y, n, Z.iso.e p, Z.iso.e q, Z.iso.chainIngredient_img hi⟩

/-- Bad-vine classification is determined by the actual molecular vine type. -/
theorem isBadVineSet_image_iff {H : Garden w} (F : MolIso G.molecule H.molecule)
    (T : Finset (GBranch G.tree)) : IsBadVineSet H (F.img T) ↔ IsBadVineSet G T := by
  constructor
  · rintro ⟨X, p, q, hbad, hv⟩
    have h := F.symm.isVine_img hv
    rw [F.img_img_symm] at h
    exact ⟨X, F.symm.e p, F.symm.e q, hbad, h⟩
  · rintro ⟨X, p, q, hbad, hv⟩
    exact ⟨X, F.e p, F.e q, hbad, F.isVine_img hv⟩

end WaveTurbulence.VineA
