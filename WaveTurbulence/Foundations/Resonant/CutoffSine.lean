/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.SineKernel
public import WaveTurbulence.Foundations.Resonant.PrincipalValueOneDim
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Uniform sine cancellation for scaled smooth cutoffs

The total variation of `χ(μ·)` is independent of `μ > 0`. Combined with the
bounded sine primitive this yields the oscillatory estimate used in DH21
Lemma 6.3, uniformly in both cutoff scale and Fourier frequency.
-/

public section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace WaveTurbulence.Resonant

/-- The derivative of a smooth compactly supported scalar cutoff is integrable. -/
theorem IsPVCutoff.integrable_deriv {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    (hs : ContDiff ℝ 1 χ) : Integrable (deriv χ) :=
  (hs.continuous_deriv le_rfl).integrable_of_hasCompactSupport hχ.compact.deriv

/-- Scaling preserves the `L¹` norm of the derivative. -/
theorem integral_abs_scaled_deriv {χ : ℝ → ℝ} (μ : ℝ) (hμ : 0 < μ) :
    (∫ t : ℝ, |-(deriv χ (μ * t) * μ)|) = ∫ t : ℝ, |deriv χ t| := by
  simp only [abs_neg, abs_mul, abs_of_pos hμ, integral_mul_const]
  rw [Measure.integral_comp_mul_left (fun t : ℝ => |deriv χ t|) μ, smul_eq_mul, abs_of_pos (inv_pos.mpr hμ)]
  field_simp

/-- The small-interval sine integral is bounded uniformly in scale and frequency. -/
theorem abs_integral_cutoff_sine_le {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    (hs : ContDiff ℝ 1 χ) {C μ : ℝ} (hC : ∀ t, |χ t| ≤ C) (hμ : 0 < μ) (η : ℝ) :
    |∫ t in (0 : ℝ)..1, (1 - χ (μ * t)) * (η * Real.sinc (η * t))| ≤
      3 * (1 + C + ∫ t : ℝ, |deriv χ t|) := by
  have hd := hs.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hdi := hχ.integrable_deriv hs
  have hscaled : Integrable (fun t => -(deriv χ (μ * t) * μ)) :=
    ((hdi.comp_mul_left' hμ.ne').mul_const μ).neg
  have hdiff : ∀ t, HasDerivAt (fun u => 1 - χ (μ * u)) (-(deriv χ (μ * t) * μ)) t := by
    intro t
    exact ((hd (μ * t)).hasDerivAt.comp t (hasDerivAt_const_mul μ)).const_sub 1
  have hvar : (∫ t in (0 : ℝ)..1, |-(deriv χ (μ * t) * μ)|) ≤
      ∫ t : ℝ, |deriv χ t| := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (setIntegral_le_integral hscaled.abs (Eventually.of_forall fun _ => abs_nonneg _)).trans_eq
      (integral_abs_scaled_deriv μ hμ)
  have ht := abs_integral_mul_sineKernel_le
    (continuous_const.sub (hχ.cont.comp (continuous_const.mul continuous_id))).continuousOn
    (fun t _ => hdiff t) hscaled.intervalIntegrable η
  refine ht.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  exact add_le_add ((abs_sub _ _).trans (by simpa using add_le_add_left (hC μ) 1)) hvar

end WaveTurbulence.Resonant
