/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.ResonantConvolution

/-! # Positivity and integrability of the frequency envelopes -/

public section

open MeasureTheory

namespace WaveTurbulence.Analysis

theorem oscillatoryWeight_pos (q : ℝ) : 0 < oscillatoryWeight q := by
  unfold oscillatoryWeight
  positivity

theorem oscillatoryWeight_le_one (q : ℝ) : oscillatoryWeight q ≤ 1 := by
  have hs : 0 < Real.sqrt (1 + q ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hb : 1 ≤ Real.sqrt (1 + q ^ 2) :=
    (Real.le_sqrt zero_le_one (by positivity)).mpr (by nlinarith only [sq_nonneg q])
  rw [oscillatoryWeight, ← one_div]
  exact (div_le_iff₀ hs).mpr (by simpa only [one_mul] using hb)

theorem cauchyWeight_le_one (q : ℝ) : cauchyWeight q ≤ 1 := by
  rw [cauchyWeight, ← one_div]
  exact (div_le_iff₀ (by positivity : 0 < 1 + q ^ 2)).mpr (by nlinarith only [sq_nonneg q])

theorem integrable_cauchyWeight : Integrable cauchyWeight := integrable_inv_one_add_sq

theorem integral_cauchyWeight : (∫ q : ℝ, cauchyWeight q) = Real.pi := integral_univ_inv_one_add_sq

theorem integral_cauchyWeight_sub (a : ℝ) : (∫ q : ℝ, cauchyWeight (q - a)) = Real.pi := by
  rw [integral_sub_right_eq_self, integral_cauchyWeight]

end WaveTurbulence.Analysis
