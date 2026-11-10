/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.Vine.A.VinePrimeState
/-! VINE-A1: the sigma-selected family is precisely the core part of V carried
by the actual S2a splice units, not a separately assumed subcollection. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist

/-- B1b: the units of an SG group cover its unmarked `𝒱`-ingredients (main's `cover` for an unmarked group, the runs'
`cover` for a marked one). -/
theorem groupUnitsMk_cover {w : ℕ} {G : Garden w} {Mk : Set (CLVine G)}
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) {c : CLVine G} (hc : c ∈ vinesV G) (hcM : c ∉ Mk)
    (hi : IsIngredient G.molecule S c.atoms) : ∃ u ∈ groupUnitsMk G Mk S, c.atoms ⊆ u.atoms := by
  classical
  by_cases hm : markedGroup G Mk S
  · have hne := exists_markedGroupUnits hm
    have he : groupUnitsMk G Mk S = (Classical.choice hne).runs := by
      unfold groupUnitsMk
      simp only [hm, ↓reduceIte, dif_pos hne]
    rw [he]
    exact (Classical.choice hne).cover c hc hcM hi
  · rw [groupUnitsMk_of_not_marked hm]
    exact (groupUnitsOf G S).cover (Mole.garden_isMolecule G) hS c hc hi

/-- B1b (Mk-general form of `vinesV0_iff_unit_cover`): unmarked `𝒱₀` membership and the cover by the units (runs at
marked groups, which exist by B2a's `exists_markedGroupUnits`) coincide on the unmarked `𝒱` carrier. -/
theorem vinesV0_iff_unit_coverMk {w : ℕ} (G : Garden w) (σ : Prescription G) {Mk : Set (CLVine G)}
    (c : CLVine G) :
    c ∈ vinesV0 G σ Mk ↔ c ∈ vinesV G ∧ c ∉ Mk ∧ ∃ u ∈ unitBlocks G σ Mk, c.atoms ⊆ u.atoms := by
  constructor
  · rintro ⟨hc, S, hS, hi, hσ, hcM⟩
    obtain ⟨u, hu, hcu⟩ := groupUnitsMk_cover hS hc hcM hi
    exact ⟨hc, hcM, u, mem_unitBlocksMk.mpr ⟨S, hS, hσ, hu⟩, hcu⟩
  · rintro ⟨hc, hcM, u, hu, hcu⟩
    have hc' := hc
    obtain ⟨S, hS, hi, hcond⟩ := hc
    obtain ⟨T, hT, hσ, hut⟩ := mem_unitBlocksMk.mp hu
    have he : S = T := by
      by_contra hne
      have hz := c.upper_mem
      exact (Finset.disjoint_left.mp (maximalGroups_disjoint (Mole.garden_isMolecule G) hS hT hne)
        (ing_subset hi hz) (groupUnitsMk_sub hut (hcu hz))).elim
    exact ⟨hc', S, hS, hi, he.symm ▸ hσ, hcM⟩

/-- B1b: `vinesV0_iff_unit_coverMk` with the unmarked carrier `𝒱 ∖ Mk` as one conjunct (the shape of
`vinesV0_iff_unit_cover`, used by the Mk-general class-C cover statements). -/
theorem vinesV0_iff_unit_cover_diffMk {w : ℕ} (G : Garden w) (σ : Prescription G) {Mk : Set (CLVine G)}
    (c : CLVine G) :
    c ∈ vinesV0 G σ Mk ↔ c ∈ vinesV G \ Mk ∧ ∃ u ∈ unitBlocks G σ Mk, c.atoms ⊆ u.atoms :=
  ⟨fun h => let ⟨a, b, d⟩ := (vinesV0_iff_unit_coverMk G σ c).mp h; ⟨⟨a, b⟩, d⟩,
    fun ⟨⟨a, b⟩, d⟩ => (vinesV0_iff_unit_coverMk G σ c).mpr ⟨a, b, d⟩⟩

end WaveTurbulence.VineA
