/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLargeDifferenceSelectors
import Mathlib.Tactic

/-! # The large-difference saving in the source Fin 3 selector convention -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Set Finset CountLemmas

theorem appb_large_difference_fin_selector_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ ξsel : Fin 3, ∀ a b r : Mom d, ∀ α β : ℝ,
    c⁻¹*L^(-γ) ≤ ‖r‖ → ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ appbWidth δ γ m L ∧
        |inner ℝ r (![latticePoint L q.1,latticePoint L q.2,
          latticePoint L q.1+latticePoint L q.2] ξsel)-β| ≤ appbWidth δ γ m L) →
      (s.card : ℝ) ≤ L^(2*((d : ℝ)-γ)-2*min γ (1-γ)/3) := by
  obtain ⟨L₀,hL₀⟩ := appb_large_difference_selectors_bound d hd γ hγ c δ hc hδ m
  refine ⟨L₀,?_⟩
  intro L hL ξsel a b r α β hr s hs
  let j : AppbPairSelector := ![AppbPairSelector.first,.second,.sum] ξsel
  have he (x y : Mom d) : j.value x y = ![x,y,x+y] ξsel := by
    fin_cases ξsel <;> rfl
  apply hL₀ L hL j a b r α β hr s
  intro q hq
  have hh := hs q hq
  refine ⟨hh.1,hh.2.1,hh.2.2.1,?_⟩
  simpa only [he] using hh.2.2.2

end WaveTurbulence.Mole
