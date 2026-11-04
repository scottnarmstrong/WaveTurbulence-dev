/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeLocalizationRadius

/-!
# Simultaneous finite localization for a finite forest

The per-tree center counts multiply to the actual total branch count.
This covers both the two trees of a couple and a single regular tree.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh.LocalizationTree

/-- The source forest has an exponential number of simultaneous vertex-center families. -/
theorem exists_finite_forest_localization (d : ℕ) : ∃ C : ℕ,
    ∀ R : ℝ, 0 < R → ∀ w : ℕ, ∀ t : Fin w → LocalizationTree,
      ∀ k0 : Fin w → Path → Mom d,
      ∃ S : Finset (Fin w → Path → Mom d), S.card ≤ C ^ (∑ i, (t i).order) ∧
        ∀ k : Fin w → Path → Mom d, (∀ i, IsDecoration (t i) (k i)) →
          (∀ i p, p ∈ (t i).leaves → ‖k i p - k0 i p‖ ≤ R) →
          ∃ c ∈ S, ∀ i p, p ∈ (t i).nodes → ‖k i p - c i p‖ ≤ R := by
  classical
  obtain ⟨C, hb⟩ := exists_finite_localization_radius d
  refine ⟨C, ?_⟩
  intro R hR w t k0
  choose S hS hs using fun i => hb R hR (t i) (k0 i)
  refine ⟨Fintype.piFinset S, ?_, ?_⟩
  · rw [Fintype.card_piFinset]
    apply (Finset.prod_le_prod (fun i _ => hS i)).trans_eq
    exact Finset.prod_pow_eq_pow_sum _ _ _
  · intro k hk hleaf
    choose c hc hclose using fun i => hs i (k i) (hk i) (hleaf i)
    exact ⟨c, Fintype.mem_piFinset.mpr hc, hclose⟩

end WaveTurbulence.Incoh.LocalizationTree
