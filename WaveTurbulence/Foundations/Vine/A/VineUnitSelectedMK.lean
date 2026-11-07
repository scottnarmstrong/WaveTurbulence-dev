/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineUnitSelected
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvMK2
import Mathlib.Tactic

/-!
# B2a MK-RUNS: `unitBlocks_selected_spine` for every marked vine set

B0 §5: the statements of the vine-side bridges hold for runs.  `unitBlocks_selected_spineMk` is main's
`unitBlocks_selected_spine` with the marked set `Mk` (at `Mk = ∅` it is main's statement): every unit of
`unitBlocks G σ Mk` (main's units of an unmarked group, the runs of a marked one) has a spine whose members are vines
of `𝒱₀♮ = vinesV0 G σ Mk`.  (`unitBlocks_chainMk` is B1a's, from the field `chain` supplied by
`exists_markedGroupUnits`.)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Vine
variable {w : ℕ} {G : Garden w}

/-- Every unit of a group (marked or not) has a spine of unmarked `𝒱`-ingredients of the group. -/
theorem groupUnitsMk_selected_spine {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) {u : CLBlock G} (hu : u ∈ groupUnitsMk G Mk S) :
    ∃ L, Spine G.molecule L u.atoms u.upper u.lower ∧ ∀ t ∈ L, ∃ c : CLVine G,
      c ∈ vinesV G ∧ c ∉ Mk ∧ IsIngredient G.molecule S c.atoms ∧ c.atoms = t.1 := by
  by_cases h : markedGroup G Mk S
  · exact groupUnitsMk_spine_of_markedMK h hu
  · rw [groupUnitsMk_of_not_marked h] at hu
    obtain ⟨L, hs, hsel⟩ := groupUnit_selected_spine (groupUnitsOf G S) hS hu
    refine ⟨L, hs, fun t ht => ?_⟩
    obtain ⟨c, hc, he⟩ := hsel t ht
    have hci : IsIngredient G.molecule S c.atoms := by
      obtain ⟨S', hS', hi', _⟩ := hc
      have hin : c.atoms ⊆ S := he ▸ (hs.mem_vine ht).2.trans ((groupUnitsOf G S).sub u hu)
      have heS : S' = S := by
        by_contra hne
        exact (disjoint_left.mp (groups_disjoint' (Mole.garden_isMolecule G) hS' hS hne)
          (ingredient_sub hi' c.upper_mem)) (hin c.upper_mem)
      exact heS ▸ hi'
    exact ⟨c, hc, not_mem_of_not_markedGroup h hc hci, hci, he⟩

/-- **`unitBlocks_selected_spine` for every marked vine set**: every unit is a spine of `𝒱₀♮` vines. -/
theorem unitBlocks_selected_spineMk {σ : Prescription G} {Mk : Set (CLVine G)} {u : CLBlock G}
    (hu : u ∈ unitBlocks G σ Mk) :
    ∃ L, Spine G.molecule L u.atoms u.upper u.lower ∧ ∀ t ∈ L, ∃ c ∈ vinesV0 G σ Mk, c.atoms = t.1 := by
  obtain ⟨S, hS, hσ, hum⟩ := mem_unitBlocksMk.mp hu
  obtain ⟨L, hs, hsel⟩ := groupUnitsMk_selected_spine hS hum
  refine ⟨L, hs, fun t ht => ?_⟩
  obtain ⟨c, hc, hcMk, hci, he⟩ := hsel t ht
  exact ⟨c, ⟨hc, S, hS, hci, hσ, hcMk⟩, he⟩

end WaveTurbulence.VineA
