/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.RadialWeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Local and exterior integrability of norm powers

The scalar and transverse integrability inputs for the anisotropic M₁ kernel.
-/

public section

open MeasureTheory Set Metric

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Norm powers are integrable on bounded balls below the dimension. -/
theorem integrableOn_ball_norm_neg_rpow (hd : 1 ≤ Module.finrank ℝ E)
    (b : ℝ) (hb : b < Module.finrank ℝ E) (R : ℝ) :
    IntegrableOn (fun x : E => ‖x‖ ^ (-b)) (ball 0 R) μ := by
  refine integrableOn_ball_of_norm_le_rpow (C := 1) hd hb ?_ ?_
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
  · exact (measurable_norm.pow_const (-b)).aestronglyMeasurable

/-- Norm powers are integrable outside a positive-radius ball above the dimension. -/
theorem integrableOn_exterior_norm_neg_rpow (b : ℝ)
    (hb : (Module.finrank ℝ E : ℝ) < b) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x : E => ‖x‖ ^ (-b)) (ball 0 R)ᶜ μ := by
  have hb0 : 0 ≤ b := (Nat.cast_nonneg _).trans hb.le
  let C : ℝ := (1 + R⁻¹) ^ b
  have hi := (integrable_one_add_norm (μ := μ) hb).const_mul C
  refine (hi.mono_measure μ.restrict_le_self).mono'
    (measurable_norm.pow_const (-b)).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hxR : R ≤ ‖x‖ := le_of_not_gt (by simpa only [mem_compl_iff, mem_ball_zero_iff] using hx)
  have hlin : 1 + ‖x‖ ≤ (1 + R⁻¹) * ‖x‖ := by
    have h := (mul_le_mul_of_nonneg_left hxR (inv_nonneg.mpr hR.le))
    rw [inv_mul_cancel₀ hR.ne'] at h
    linarith only [h]
  exact rpow_neg_le_of_le_mul (by positivity) (hR.trans_le hxR) (by positivity) hb0 hlin

end WaveTurbulence.WKEL2
