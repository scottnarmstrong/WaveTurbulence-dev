/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSelected
/-! Actual source and target units cover one another under the unit twist's
atom bijection, using selected ingredient spines and their overlap. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- Ingredient spines transport with a literal molecule isomorphism. -/
theorem spine_image {V D V' D' : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    [DecidableEq V'] [Fintype D'] [DecidableEq D']
    {M : Molecule V D} {N : Molecule V' D'} (F : MolIso M N)
    {L : List (Finset V × V × V)} {S : Finset V} {a b : V} (hs : Spine M L S a b) :
    Spine N (L.map (fun t => (F.img t.1, F.e t.2.1, F.e t.2.2))) (F.img S) (F.e a) (F.e b) := by
  induction hs with
  | one hv => exact .one (F.isSomeVine_img hv)
  | snoc hs hv hi hne ih =>
    rw [List.map_append, List.map_singleton, F.img_union]
    apply Spine.snoc ih (F.isSomeVine_img hv) _ (F.e.injective.ne hne)
    rw [← F.img_inter, hi, F.img_singleton]

/-- The image of an actual source unit is contained in a single actual target unit. -/
theorem unitBlocks_image_subset (Z : TwistGroupSite G) (σ : Prescription G)
    {u : CLBlock G} (hu : u ∈ unitBlocks G σ) :
    ∃ v ∈ unitBlocks Z.target (transportPrescription Z.iso σ), Z.iso.img u.atoms ⊆ v.atoms := by
  obtain ⟨L, hs, hsel⟩ := unitBlocks_selected_spine hu
  apply spine_cover_one_unit _ (unitBlocks_pairwise (Mole.garden_isMolecule Z.target) _) (spine_image Z.iso hs)
  intro t ht
  obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
  obtain ⟨c, hc, he⟩ := hsel t0 ht0
  obtain ⟨c', hc', hat, _, _⟩ := vinesV0_image Z σ hc
  obtain ⟨_, v, hv, hcv⟩ := (vinesV0_iff_unit_cover _ _ c').mp hc'
  refine ⟨v, hv, ?_⟩
  rw [hat, he] at hcv
  exact hcv

/-- The inverse image of an actual target unit lies in an actual source unit. -/
theorem unitBlocks_preimage_subset (Z : TwistGroupSite G) (σ : Prescription G)
    {v : CLBlock Z.target} (hv : v ∈ unitBlocks Z.target (transportPrescription Z.iso σ)) :
    ∃ u ∈ unitBlocks G σ, Z.iso.symm.img v.atoms ⊆ u.atoms := by
  obtain ⟨L, hs, hsel⟩ := unitBlocks_selected_spine hv
  apply spine_cover_one_unit _ (unitBlocks_pairwise (Mole.garden_isMolecule G) _) (spine_image Z.iso.symm hs)
  intro t ht
  obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
  obtain ⟨c', hc', he⟩ := hsel t0 ht0
  obtain ⟨c, hc, hat, _, _⟩ := vinesV0_preimage Z σ hc'
  obtain ⟨_, u, hu, hcu⟩ := (vinesV0_iff_unit_cover _ _ c).mp hc
  refine ⟨u, hu, ?_⟩
  rw [← he, hat, Z.iso.img_img_symm]
  exact hcu

end WaveTurbulence.VineA
