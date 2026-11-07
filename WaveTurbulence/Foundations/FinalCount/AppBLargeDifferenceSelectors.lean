/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLargeDifferencePairX
public import WaveTurbulence.Foundations.FinalCount.AppBLargeDifferencePairSum
import Mathlib.Tactic

/-! # Uniform large-difference estimates for all three selectors -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset CountLemmas

inductive AppbPairSelector where
  | first | second | sum
  deriving DecidableEq

def AppbPairSelector.value {d : ℕ} (j : AppbPairSelector) (x y : Mom d) : Mom d :=
  match j with
  | .first => x
  | .second => y
  | .sum => x+y

/-- All three selectors have a common threshold, independent of the
conserved vector, centers, and finite subset. -/
theorem appb_large_difference_selectors_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ j : AppbPairSelector, ∀ a b r : Mom d, ∀ α β : ℝ,
    c⁻¹*L^(-γ) ≤ ‖r‖ → ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ appbWidth δ γ m L ∧
        |inner ℝ r (j.value (latticePoint L q.1) (latticePoint L q.2))-β| ≤ appbWidth δ γ m L) →
      (s.card : ℝ) ≤ L^(2*((d : ℝ)-γ)-2*min γ (1-γ)/3) := by
  classical
  obtain ⟨Lx,hx⟩ := appb_large_difference_pair_x_bound d hd γ hγ c δ hc hδ m
  obtain ⟨Ls,hsum⟩ := appb_large_difference_pair_sum_bound d hd γ hγ c δ hc hδ m
  refine ⟨max Lx Ls,?_⟩
  intro L hL j a b r α β hr s hs
  have hLx := (le_max_left Lx Ls).trans hL
  have hLs := (le_max_right Lx Ls).trans hL
  cases j with
  | first => exact hx L hLx a b r α β hr s hs
  | sum => exact hsum L hLs a b r α β hr s hs
  | second =>
    have hb := hx L hLx b a r α β hr (s.image Prod.swap) (by
      intro q hq
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
      have hp' := hs p hp
      exact ⟨hp'.2.1,hp'.1,by simpa only [Prod.swap, real_inner_comm] using hp'.2.2.1,hp'.2.2.2⟩)
    simpa only [card_image_of_injective s Prod.swap_injective] using hb

end WaveTurbulence.Mole
