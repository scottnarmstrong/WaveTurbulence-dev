/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.InductParameters
/-! Elementary strict theta gap and scale absorption for the next spatial remainder. -/
public section
namespace WaveTurbulence.Induct

theorem two_power_le_half_of_gap {L s θ : ℝ} (hL : 0 < L)
    (hgap : 4 ≤ L ^ (s - θ)) : 2 * L ^ (-s) ≤ (1 / 2) * L ^ (-θ) := by
  have hp : 0 < L ^ (s - θ) := Real.rpow_pos_of_pos hL _
  have hi : (L ^ (s - θ))⁻¹ ≤ 1 / 4 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hgap
  have he : L ^ (-s) = L ^ (-θ) * (L ^ (s - θ))⁻¹ := by
    rw [← Real.rpow_neg hL.le, ← Real.rpow_add hL]
    congr 1
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hL.le (-θ))
  nlinarith

theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-1)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hh
  linarith

end WaveTurbulence.Induct
