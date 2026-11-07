/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPairGrowth
public import WaveTurbulence.Foundations.CountLemmas.PairCoarse
public import WaveTurbulence.Foundations.CountLemmas.CoefficientGap
import Mathlib.Tactic

/-! # Appendix B: the power saving for a large conserved difference

The counting problem is an actual dot-product band and an independent
strip. Polynomial logarithmic energy windows are included explicitly.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Filter Finset CountLemmas

/-- DH23 basiccount(3), large-difference geometry, selector x. The threshold
is uniform in all centers, the conserved vector and the finite subset. -/
theorem appb_large_difference_pair_x_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (m : ℕ) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ a b r : Mom d, ∀ α β : ℝ,
    c⁻¹*L^(-γ) ≤ ‖r‖ → ∀ s : Finset ((Fin d → ℤ) × (Fin d → ℤ)),
      (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ appbWidth δ γ m L ∧
        |inner ℝ r (latticePoint L q.1)-β| ≤ appbWidth δ γ m L) →
      (s.card : ℝ) ≤ L^(2*((d : ℝ)-γ)-2*min γ (1-γ)/3) := by
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp
    ((appb_pair_x_majorant_eventual d hd c δ γ hγ m).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨L₀,?_⟩
  intro L hL a b r α β hr s hs
  obtain ⟨hmajor,hL1⟩ := hL₀ L hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hτ : 0 ≤ appbWidth δ γ m L := by unfold appbWidth; positivity
  obtain ⟨i,hi,hgap⟩ := exists_strip_coordinate (by omega : 0 < d) r
    (Real.rpow_pos_of_pos hLp (-γ)) hc hr
  have hraw := card_pair_coarse_le hd s hL1 hτ a b r α β i (abs_pos.mp hi) hs
  have hcoef : 2*appbWidth δ γ m L*L/|r i|+1 ≤
      1+(2*(d : ℝ)*c)*(appbWidth δ γ m L*L/L^(-γ)) := by
    have hh := inverse_strip_coefficient_le hLp.le hτ hi hgap
    convert hh using 1 <;> ring
  have hfac : 0 ≤ 12*((d : ℝ)+1)*(3^(d-1)*L^(d-1))^2 := by positivity
  have htail : 0 ≤ 1+appbWidth δ γ m L*L := by positivity
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hfac) htail
  calc
    (s.card : ℝ) ≤ 15^d*L^d+12*((d : ℝ)+1)*(3^(d-1)*L^(d-1))^2*
      (2*appbWidth δ γ m L*L/|r i|+1)*(1+appbWidth δ γ m L*L) := hraw
    _ ≤ appbPairXMajorant d c δ γ m L := by
      unfold appbPairXMajorant
      exact add_le_add le_rfl hh
    _ ≤ _ := hmajor

end WaveTurbulence.Mole
