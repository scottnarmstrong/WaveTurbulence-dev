/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CutoffFourierDecay

/-!
# Exact nonzero-frequency formula for the cutoff time kernel

The two Fourier translates are the two binary choices in the tree bound.
-/

public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace WaveTurbulence.Analysis

theorem timePhase_add (q r t : ℝ) : timePhase q t * timePhase r t = timePhase (q + r) t := by
  unfold timePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Explicit primitive at nonzero frequency. -/
theorem timePrimitive_eq_of_ne_zero (a q t : ℝ) (hq : q ≠ 0) :
    timePrimitive a q t = (timePhase q t - timePhase q a) / ((2 * Real.pi * q : ℂ) * Complex.I) := by
  have hc : (2 * Real.pi * q : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero _ Complex.I_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr hq)
  have heq : timePhase q = (fun s : ℝ => Complex.exp (((2 * Real.pi * q : ℂ) * Complex.I) * s)) := by
    funext s
    unfold timePhase
    congr 1
    push_cast
    ring
  rw [timePrimitive, heq, integral_exp_mul_complex hc]

/-- Fourier transform written with `timePhase`. -/
theorem fourier_eq_timePhase (f : ℝ → ℂ) (t : ℝ) :
    𝓕 f t = ∫ s : ℝ, timePhase (-t) s * f s := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with s
  rw [smul_eq_mul]
  congr 1
  unfold timePhase
  congr 1
  push_cast
  ring

private theorem integrable_timePhase_mul {f : ℝ → ℂ} (hf : Integrable f) (q : ℝ) :
    Integrable (fun s : ℝ => timePhase q s * f s) := by
  apply hf.norm.mono' ((contDiff_timePhase q).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards with s
  change ‖timePhase q s * f s‖ ≤ ‖f s‖
  rw [norm_mul, norm_timePhase, one_mul]

/-- Exact formula for nonzero frequency. The lower endpoint contributes
only a unimodular coefficient to the zero-centred Fourier term. -/
theorem cutoffTimeKernel_eq_of_ne_zero {χ : ℝ → ℂ} (hχ : Integrable χ)
    (a t q : ℝ) (hq : q ≠ 0) :
    cutoffTimeKernel χ a t q =
      (𝓕 χ (t - q) - timePhase q a * 𝓕 χ t) / ((2 * Real.pi * q : ℂ) * Complex.I) := by
  have hf : (fun s : ℝ => timePhase (-t) s * cutoffPrimitive χ a q s) =
      (fun s : ℝ => (timePhase (q - t) s * χ s -
        timePhase q a * (timePhase (-t) s * χ s)) / ((2 * Real.pi * q : ℂ) * Complex.I)) := by
    funext s
    rw [cutoffPrimitive, timePrimitive_eq_of_ne_zero a q s hq]
    calc
      _ = ((timePhase (-t) s * timePhase q s) * χ s -
          timePhase q a * (timePhase (-t) s * χ s)) / ((2 * Real.pi * q : ℂ) * Complex.I) := by ring
      _ = _ := by rw [timePhase_add, neg_add_eq_sub]
  rw [cutoffTimeKernel, fourier_eq_timePhase, hf, integral_div,
    integral_sub (integrable_timePhase_mul hχ (q - t))
      ((integrable_timePhase_mul hχ (-t)).const_mul (timePhase q a)), integral_const_mul]
  have he : (∫ s : ℝ, timePhase (q - t) s * χ s) = 𝓕 χ (t - q) := by
    rw [fourier_eq_timePhase, neg_sub]
  rw [he, ← fourier_eq_timePhase]

end WaveTurbulence.Analysis
