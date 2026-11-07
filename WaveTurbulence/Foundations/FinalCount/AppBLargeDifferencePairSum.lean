/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPairSumGrowth
public import WaveTurbulence.Foundations.CountLemmas.PairSumCoarse
import Mathlib.Tactic

/-! # Appendix B: the large-difference estimate with selector x+y -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Filter Finset CountLemmas

/-- Uniform power saving for the sum selector, including polynomial
logarithmic windows and unrestricted centers. -/
theorem appb_large_difference_pair_sum_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ a b r : Mom d, ∀ α β : ℝ,
    c⁻¹*L^(-γ) ≤ ‖r‖ → ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ appbWidth δ γ m L ∧
        |inner ℝ r (latticePoint L q.1+latticePoint L q.2)-β| ≤ appbWidth δ γ m L) →
      (s.card : ℝ) ≤ L^(2*((d : ℝ)-γ)-2*min γ (1-γ)/3) := by
  obtain ⟨n,rfl⟩ : ∃ n, d = n+2 := ⟨d-2,by omega⟩
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp
    (((appb_pair_sum_majorant_eventual n c δ γ hγ m).and
      (appb_width_times_sq_eventually_ge_one δ γ hδ hγ.2 m)).and
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨L₀,?_⟩
  intro L hL a b r α β hr s hs
  obtain ⟨⟨hmajor,hW⟩,hL1⟩ := hL₀ L hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hτ : 0 ≤ appbWidth δ γ m L := by unfold appbWidth; positivity
  have hA : 0 < c⁻¹*L^(-γ) := mul_pos (inv_pos.mpr hc) (Real.rpow_pos_of_pos hLp _)
  have hraw := card_pair_sum_strip_coarse_le s hL1 hτ hA hW a b r α β hr hs
  have he : 2*((n+2 : ℕ) : ℝ)*appbWidth δ γ m L*L/(c⁻¹*L^(-γ))+1 =
      1+(2*((n+2 : ℕ) : ℝ)*c)*(appbWidth δ γ m L*L/L^(-γ)) := by
    field_simp
    <;> ring
  rw [he] at hraw
  exact hraw.trans hmajor

end WaveTurbulence.Mole
