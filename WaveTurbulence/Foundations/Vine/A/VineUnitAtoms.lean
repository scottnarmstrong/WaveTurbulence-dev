/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitList
/-! Actual unit atom sets transport under every ingredient unit-twist site,
without requiring that the active group is prescribed SG. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- The atom image of every actual source unit is an actual target unit. -/
theorem unitBlocks_image_atoms (Z : TwistGroupSite G) (σ : Prescription G)
    {u : CLBlock G} (hu : u ∈ unitBlocks G σ) :
    ∃ v ∈ unitBlocks Z.target (transportPrescription Z.iso σ), v.atoms = Z.iso.img u.atoms := by
  obtain ⟨v, hv, hUv⟩ := unitBlocks_image_subset Z σ hu
  obtain ⟨u', hu', hvU'⟩ := unitBlocks_preimage_subset Z σ hv
  have hUU' : u.atoms ⊆ u'.atoms := by
    have h := (Z.iso.symm.img_subset_iff).mpr hUv
    rw [Z.iso.img_img_symm] at h
    exact h.trans hvU'
  have he : u = u' := units_eq_of_mem_inter _ (unitBlocks_pairwise (Mole.garden_isMolecule G) σ)
    hu hu' u.isBlock.2.1 (hUU' u.isBlock.2.1)
  subst u'
  have hvU : v.atoms ⊆ Z.iso.img u.atoms := by
    have h := (Z.iso.img_subset_iff).mpr hvU'
    rw [Z.iso.img_symm_img] at h
    exact h
  exact ⟨v, hv, subset_antisymm hvU hUv⟩

/-- Every actual target unit atom set comes from an actual source unit. -/
theorem unitBlocks_preimage_atoms (Z : TwistGroupSite G) (σ : Prescription G)
    {v : CLBlock Z.target} (hv : v ∈ unitBlocks Z.target (transportPrescription Z.iso σ)) :
    ∃ u ∈ unitBlocks G σ, v.atoms = Z.iso.img u.atoms := by
  obtain ⟨u, hu, hvu⟩ := unitBlocks_preimage_subset Z σ hv
  obtain ⟨v', hv', hat⟩ := unitBlocks_image_atoms Z σ hu
  have hsub : v.atoms ⊆ v'.atoms := by
    have h := (Z.iso.img_subset_iff).mpr hvu
    rw [Z.iso.img_symm_img, ← hat] at h
    exact h
  have he : v = v' := units_eq_of_mem_inter _ (unitBlocks_pairwise (Mole.garden_isMolecule Z.target) _)
    hv hv' v.isBlock.2.1 (hsub v.isBlock.2.1)
  exact ⟨u, hu, (congrArg CLBlock.atoms he).trans hat⟩

/-- Actual unit atom lists transport under every unit-twist site and prescription. -/
theorem unitBlocks_atoms_perm (Z : TwistGroupSite G) (σ : Prescription G) :
    ((unitBlocks G σ).map (fun u => Z.iso.img u.atoms)).Perm
      ((unitBlocks Z.target (transportPrescription Z.iso σ)).map CLBlock.atoms) := by
  apply (List.perm_ext_iff_of_nodup
    ((unitBlocks_nodup σ).map (fun _ _ h => clBlock_eq_of_atoms (Z.iso.img_injective h)))
    ((unitBlocks_nodup (transportPrescription Z.iso σ)).map (fun _ _ h => clBlock_eq_of_atoms h))).mpr
  intro A
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
    obtain ⟨v, hv, he⟩ := unitBlocks_image_atoms Z σ hu
    exact List.mem_map.mpr ⟨v, hv, he⟩
  · intro h
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    obtain ⟨u, hu, he⟩ := unitBlocks_preimage_atoms Z σ hv
    exact List.mem_map.mpr ⟨u, hu, he.symm⟩

end WaveTurbulence.VineA
