/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineChosenIncoherency
public import WaveTurbulence.Foundations.Vine.A.VineFineBatch
/-! The exact unit-ingredient carrier follows every actual selected-family
batch, derived from the already proved actual chosen unit-list transport. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist
variable {w : ℕ} {G H : Garden w}

/-- Ingredient transport follows from actual atom-list transport, independently of unit order. -/
theorem unitIngredients_image_iff_of_units (F : MolIso G.molecule H.molecule)
    (σ : Prescription G) (τ : Prescription H)
    (hp : ((unitBlocks G σ).map (fun u => F.img u.atoms)).Perm ((unitBlocks H τ).map CLBlock.atoms))
    (T : Finset (GBranch G.tree)) : F.img T ∈ unitIngredients H τ ↔ T ∈ unitIngredients G σ := by
  constructor
  · rintro ⟨v, hv, x, y, n, p, q, hi⟩
    have hl : v.atoms ∈ (unitBlocks G σ).map (fun u => F.img u.atoms) :=
      hp.mem_iff.mpr (List.mem_map.mpr ⟨v, hv, rfl⟩)
    obtain ⟨u, hu, he⟩ := List.mem_map.mp hl
    have hi' := F.symm.chainIngredient_img hi
    rw [← he, F.img_img_symm, F.img_img_symm] at hi'
    exact ⟨u, hu, F.symm.e x, F.symm.e y, n, F.symm.e p, F.symm.e q, hi'⟩
  · rintro ⟨u, hu, x, y, n, p, q, hi⟩
    have hl : F.img u.atoms ∈ (unitBlocks H τ).map CLBlock.atoms :=
      hp.mem_iff.mp (List.mem_map.mpr ⟨u, hu, rfl⟩)
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hl
    refine ⟨v, hv, F.e x, F.e y, n, F.e p, F.e q, ?_⟩
    rw [he]
    exact F.chainIngredient_img hi

/-- The ingredient carrier transports along the actual composed selected-family batch. -/
theorem BatchIso.unitIngredients {p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (T : Finset (GBranch A.skeleton.tree)) :
    F.img T ∈ unitIngredients B.skeleton (transportPrescription F σ) ↔ T ∈ unitIngredients A.skeleton σ :=
  unitIngredients_image_iff_of_units F σ _ (h.units σ hA) T

end WaveTurbulence.VineA
