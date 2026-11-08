/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitImageCover
/-! Choice-independent transport of the actual unitBlocks list under a
selected unit LF twist. Forward and inverse spine containment force equality. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- B1b-2 (Mk-general form of `unitImage_mem`, two marked sets carried by the twist). -/
theorem unitImage_memMk (Z : TwistGroupSite G) (σ : Prescription G) {Mk : Set (CLVine G)}
    {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    {u : CLBlock G} (hu : u ∈ unitBlocks G σ Mk) :
    unitImage Z u (unitBlocks_goodMk Z σ hsel hu) ∈
      unitBlocks Z.target (transportPrescription Z.iso σ) Mk' := by
  obtain ⟨v, hv, hUv⟩ := unitBlocks_image_subsetMk Z σ hT hu
  obtain ⟨u', hu', hvU'⟩ := unitBlocks_preimage_subsetMk Z σ hT hv
  have hUU' : u.atoms ⊆ u'.atoms := by
    have h := (Z.iso.symm.img_subset_iff).mpr hUv
    rw [Z.iso.img_img_symm] at h
    exact h.trans hvU'
  have he : u = u' := units_eq_of_mem_inter _ (unitBlocks_pairwiseMk (Mole.garden_isMolecule G) σ Mk)
    hu hu' u.isBlock.2.1 (hUU' u.isBlock.2.1)
  subst u'
  have hvU : v.atoms ⊆ Z.iso.img u.atoms := by
    have h := (Z.iso.img_subset_iff).mpr hvU'
    rw [Z.iso.img_symm_img] at h
    exact h
  have hev : v = unitImage Z u (unitBlocks_goodMk Z σ hsel hu) :=
    clBlock_eq_of_atoms (subset_antisymm hvU hUv)
  exact hev ▸ hv

/-- The transported CL block is a member of the actual target unit list. -/
theorem unitImage_mem (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    {u : CLBlock G} (hu : u ∈ unitBlocks G σ) :
    unitImage Z u (unitBlocks_good Z σ hsel hu) ∈
      unitBlocks Z.target (transportPrescription Z.iso σ) :=
  unitImage_memMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel hu

/-- B1b-2 (Mk-general form of `unitBlocks_preimage`). -/
theorem unitBlocks_preimageMk (Z : TwistGroupSite G) (σ : Prescription G) {Mk : Set (CLVine G)}
    {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    {v : CLBlock Z.target} (hv : v ∈ unitBlocks Z.target (transportPrescription Z.iso σ) Mk') :
    ∃ u ∈ unitBlocks G σ Mk, v.atoms = Z.iso.img u.atoms ∧
      v.upper = Z.iso.e u.upper ∧ v.lower = Z.iso.e u.lower := by
  obtain ⟨u, hu, hvu⟩ := unitBlocks_preimage_subsetMk Z σ hT hv
  let u' := unitImage Z u (unitBlocks_goodMk Z σ hsel hu)
  have hu' : u' ∈ unitBlocks Z.target (transportPrescription Z.iso σ) Mk' := unitImage_memMk Z σ hT hsel hu
  have hsub : v.atoms ⊆ u'.atoms := by
    have h := (Z.iso.img_subset_iff).mpr hvu
    rw [Z.iso.img_symm_img] at h
    exact h
  have he : v = u' := units_eq_of_mem_inter _
    (unitBlocks_pairwiseMk (Mole.garden_isMolecule Z.target) _ Mk') hv hu' v.isBlock.2.1 (hsub v.isBlock.2.1)
  exact ⟨u, hu, congrArg CLBlock.atoms he, congrArg CLBlock.upper he, congrArg CLBlock.lower he⟩

/-- Every actual target unit is the image of an actual source unit. -/
theorem unitBlocks_preimage (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    {v : CLBlock Z.target} (hv : v ∈ unitBlocks Z.target (transportPrescription Z.iso σ)) :
    ∃ u ∈ unitBlocks G σ, v.atoms = Z.iso.img u.atoms ∧
      v.upper = Z.iso.e u.upper ∧ v.lower = Z.iso.e u.lower :=
  unitBlocks_preimageMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel hv

/-- B1b-2 (Mk-general form of `unitBlocksEquiv`): source and target runs/units are bijective. -/
noncomputable def unitBlocksEquivMk (Z : TwistGroupSite G) (σ : Prescription G) {Mk : Set (CLVine G)}
    {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) :
    {u : CLBlock G // u ∈ unitBlocks G σ Mk} ≃
      {v : CLBlock Z.target // v ∈ unitBlocks Z.target (transportPrescription Z.iso σ) Mk'} := by
  let f : {u : CLBlock G // u ∈ unitBlocks G σ Mk} →
      {v : CLBlock Z.target // v ∈ unitBlocks Z.target (transportPrescription Z.iso σ) Mk'} :=
    fun u => ⟨unitImage Z u.1 (unitBlocks_goodMk Z σ hsel u.2), unitImage_memMk Z σ hT hsel u.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v he
    exact Subtype.ext (unitImage_injective Z (unitBlocks_goodMk Z σ hsel u.2)
      (unitBlocks_goodMk Z σ hsel v.2) (congrArg Subtype.val he))
  · intro v
    obtain ⟨u, hu, he, _, _⟩ := unitBlocks_preimageMk Z σ hT hsel v.2
    exact ⟨⟨u, hu⟩, Subtype.ext (clBlock_eq_of_atoms he.symm)⟩

/-- Actual source and target unit carriers are bijective, independently of list choices. -/
noncomputable def unitBlocksEquiv (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    {u : CLBlock G // u ∈ unitBlocks G σ} ≃
      {v : CLBlock Z.target // v ∈ unitBlocks Z.target (transportPrescription Z.iso σ)} :=
  unitBlocksEquivMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel

/-- B1b-2 (Mk-general form of `unitBlocksEquiv_spec`). -/
theorem unitBlocksEquiv_specMk (Z : TwistGroupSite G) (σ : Prescription G) {Mk : Set (CLVine G)}
    {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (u : {u : CLBlock G // u ∈ unitBlocks G σ Mk}) :
    ((unitBlocksEquivMk Z σ hT hsel) u).1.atoms = Z.iso.img u.1.atoms ∧
    ((unitBlocksEquivMk Z σ hT hsel) u).1.upper = Z.iso.e u.1.upper ∧
    ((unitBlocksEquivMk Z σ hT hsel) u).1.lower = Z.iso.e u.1.lower := by
  exact ⟨rfl, rfl, rfl⟩

/-- The chosen unit-carrier bijection has the literal source molecular coordinates. -/
theorem unitBlocksEquiv_spec (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (u : {u : CLBlock G // u ∈ unitBlocks G σ}) :
    ((unitBlocksEquiv Z σ hsel) u).1.atoms = Z.iso.img u.1.atoms ∧
    ((unitBlocksEquiv Z σ hsel) u).1.upper = Z.iso.e u.1.upper ∧
    ((unitBlocksEquiv Z σ hsel) u).1.lower = Z.iso.e u.1.lower :=
  unitBlocksEquiv_specMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel u

end WaveTurbulence.VineA
