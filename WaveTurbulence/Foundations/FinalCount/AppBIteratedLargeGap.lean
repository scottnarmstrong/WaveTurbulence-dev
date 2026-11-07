/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLargeGap
public import WaveTurbulence.Foundations.FinalCount.AppBPairGoodGain
import Mathlib.Tactic

/-! # Polylogarithmically many source reinsertion errors preserve half the gap -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Filter

theorem appb_polylog_gap_loss_eventual (γ η : ℝ) (hη : 0 < η) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ, (n : ℝ) ≤ (1+Real.log L)^m →
      L^(-γ+η)/2 ≤ L^(-γ+η)-(n : ℝ)*L^(-γ) := by
  have h := appb_log_coefficient_eventual 2 1 (-γ) (-γ+η) m (by linarith only [hη])
  filter_upwards [h,eventually_ge_atTop (1 : ℝ)] with L hL hL1 n hn
  apply appb_iterated_gap_half
  have hp : 0 ≤ L^(-γ) := Real.rpow_nonneg (zero_le_one.trans hL1) _
  have hh := mul_le_mul_of_nonneg_right hn hp
  have hc : 2*(1+Real.log L)^m*L^(-γ) ≤ L^(-γ+η) := by
    simpa only [inv_one,mul_one] using hL
  nlinarith only [hh,hc]

/-- A fixed half-factor in the source LG threshold permits a smaller
positive exponent parameter, leaving the original fine target unchanged
when combined with the stronger three-quarter fine saving. -/
theorem appb_half_gap_comparison_eventual (γ η : ℝ) (hη : 0 < η) :
    ∀ᶠ L : ℝ in atTop,L^(-γ+2*η/3) ≤ L^(-γ+η)/2 := by
  have h := appb_log_coefficient_eventual 2 1 (-γ+2*η/3) (-γ+η) 0 (by linarith only [hη])
  filter_upwards [h] with L hL
  have hh : 2*L^(-γ+2*η/3) ≤ L^(-γ+η) := by
    simpa only [pow_zero,inv_one,mul_one] using hL
  linarith only [hh]

end WaveTurbulence.Mole
