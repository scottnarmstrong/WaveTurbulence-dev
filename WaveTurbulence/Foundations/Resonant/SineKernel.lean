/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.SineIntegral

/-!
# Oscillatory sine-kernel bounds with an amplitude

A bounded sine primitive transfers the frequency to an integration-by-parts
identity, leaving a bound by the endpoint value and the total variation of the
amplitude. This bound is uniform in the frequency.
-/

public section

open MeasureTheory Set
open scoped Topology

namespace WaveTurbulence

/-- Differentiation of the primitive at an arbitrary Fourier frequency. -/
theorem hasDerivAt_sinePrimitive_mul (η t : ℝ) :
    HasDerivAt (fun u => sinePrimitive (η * u)) (η * Real.sinc (η * t)) t := by
  simpa only [Function.comp_def, mul_comm] using
    (hasDerivAt_sinePrimitive (η * t)).comp t (hasDerivAt_const_mul η)

/-- A total-variation bound for the sine kernel, uniform in the frequency `η`. -/
theorem abs_integral_mul_sineKernel_le
    {g g' : ℝ → ℝ} (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (g' t) t)
    (hi : IntervalIntegrable g' volume 0 1) (η : ℝ) :
    |∫ t in (0 : ℝ)..1, g t * (η * Real.sinc (η * t))| ≤
      3 * (|g 1| + ∫ t in (0 : ℝ)..1, |g' t|) := by
  have hv : Continuous (fun t => sinePrimitive (η * t)) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_sinePrimitive_mul η t).continuousAt
  have hs : Continuous (fun t => η * Real.sinc (η * t)) :=
    continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := g) (u' := g') (v := fun t => sinePrimitive (η * t))
    (v' := fun t => η * Real.sinc (η * t))
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hg)
    hv.continuousOn
    (by simpa only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1),
      max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using hderiv)
    (fun t _ => hasDerivAt_sinePrimitive_mul η t) hi (hs.intervalIntegrable 0 1)
  simp only [mul_zero, mul_one, sinePrimitive_zero, mul_zero, sub_zero] at hip
  have hrem : |∫ t in (0 : ℝ)..1, g' t * sinePrimitive (η * t)| ≤
      3 * ∫ t in (0 : ℝ)..1, |g' t| := by
    rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall fun t _ => ?_) (hi.abs.const_mul 3)
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_sinePrimitive_le _) (abs_nonneg _)).trans_eq (by ring)
  rw [hip]
  calc |g 1 * sinePrimitive η - ∫ t in (0 : ℝ)..1, g' t * sinePrimitive (η * t)|
      ≤ |g 1 * sinePrimitive η| + |∫ t in (0 : ℝ)..1, g' t * sinePrimitive (η * t)| := abs_sub _ _
    _ ≤ |g 1| * 3 + 3 * ∫ t in (0 : ℝ)..1, |g' t| := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (abs_sinePrimitive_le η) (abs_nonneg _)) hrem
    _ = _ := by ring

end WaveTurbulence
