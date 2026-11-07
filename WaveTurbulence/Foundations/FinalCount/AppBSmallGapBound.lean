/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBSmallGapBall
public import WaveTurbulence.Foundations.FinalCount.AppBSmallGapGrowth
import Mathlib.Tactic

/-! # Uniform counting gain for the small internal-gap branch -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Filter Finset CountLemmas

/-- DH23 Appendix B small-gap branch: the raw saving is strictly stronger
than 5 gamma0/8, leaving room for the bounded logarithmic ladder loss. -/
theorem appb_small_gap_bound (d : ℕ) (hd : 3 ≤ d) (δ γ : ℝ)
    (hδ : 0 < δ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ b : Mom d, ∀ α : ℝ,
    ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, ‖latticePoint L q.1‖ ≤ L^(-γ+2*min γ (1-γ)/3) ∧
        NearLattice L b q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ appbWidth δ γ m L) →
      (s.card : ℝ) ≤ L^(2*((d : ℝ)-γ)-31*min γ (1-γ)/48) := by
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp
    ((appb_small_gap_majorant_eventual d hd δ γ hγ m).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨L₀,?_⟩
  intro L hL b α s hs
  obtain ⟨hmajor,hL1⟩ := hL₀ L hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hg0 : 0 < min γ (1-γ) := lt_min hγ.1 (sub_pos.mpr hγ.2)
  have hR : 0 < L^(-γ+2*min γ (1-γ)/3) := Real.rpow_pos_of_pos hLp _
  have hLR : 1 ≤ L*L^(-γ+2*min γ (1-γ)/3) := by
    have he : L*L^(-γ+2*min γ (1-γ)/3) = L^(1+(-γ+2*min γ (1-γ)/3)) := by
      simpa only [Real.rpow_one] using
        (Real.rpow_add hLp (1 : ℝ) (-γ+2*min γ (1-γ)/3)).symm
    rw [he]
    apply Real.one_le_rpow hL1
    linarith only [hγ.2,hg0]
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hτ : 0 ≤ appbWidth δ γ m L := by unfold appbWidth; positivity
  have hraw := appb_pair_small_gap_ball_le (by omega : 2 ≤ d) s hL1 hτ hR hLR b α hs
  exact hraw.trans hmajor

end WaveTurbulence.Mole
