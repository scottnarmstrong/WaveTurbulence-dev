/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.CutoffSine
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# The central principal-value Fourier integral

On the symmetric unit interval the cosine contribution vanishes and the sine
contribution is controlled by the bounded primitive. This preserves uniformity
in the Fourier frequency and the truncation scale.
-/

public section

open MeasureTheory Set
open scoped Topology ContDiff

namespace WaveTurbulence

/-- The unit-modulus Fourier phase. Frequencies absorb the source's `2π`. -/
@[expose] noncomputable def unitPhase (η t : ℝ) : ℂ :=
  Complex.exp ((η * t : ℝ) * Complex.I)

theorem continuous_unitPhase (η : ℝ) : Continuous (unitPhase η) := by
  unfold unitPhase
  fun_prop

@[simp] theorem norm_unitPhase (η t : ℝ) : ‖unitPhase η t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (η * t)

/-- Reflection identity on the symmetric unit interval. -/
theorem integral_symm_unit_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Continuous f) :
    (∫ t in (-1 : ℝ)..1, f t) = ∫ t in (0 : ℝ)..1, f (-t) + f t := by
  have hneg : (∫ t in (-1 : ℝ)..0, f t) = ∫ t in (0 : ℝ)..1, f (-t) := by
    simpa only [neg_zero, neg_neg] using
      (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := (1 : ℝ)) f).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-1) 0) (hf.intervalIntegrable 0 1), hneg]
  exact (intervalIntegral.integral_add
    ((hf.comp continuous_neg).intervalIntegrable 0 1) (hf.intervalIntegrable 0 1)).symm

/-- Exact sine cancellation for the central truncated Fourier kernel. -/
theorem integral_centralFourier_eq {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (μ η : ℝ) :
    (∫ t in (-1 : ℝ)..1, (((1 - χ (μ * t)) / t : ℝ) : ℂ) * unitPhase η t) =
      2 * Complex.I * (∫ t in (0 : ℝ)..1,
        (1 - χ (μ * t)) * (η * Real.sinc (η * t)) : ℝ) := by
  have hc : Continuous (fun t : ℝ => (((1 - χ (μ * t)) / t : ℝ) : ℂ) * unitPhase η t) :=
    (Complex.continuous_ofReal.comp (hχ.continuous_div μ)).mul (continuous_unitPhase η)
  rw [integral_symm_unit_eq hc, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only
  by_cases hz : t = 0
  · subst t
    simp [unitPhase, hχ.near.eq_of_nhds]
  · have hq : (1 - χ (μ * -t)) / -t = -((1 - χ (μ * t)) / t) := by
      rw [mul_neg, hχ.even, div_neg]
    rw [hq]
    simp only [unitPhase, mul_neg, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    have hs : η * Real.sinc (η * t) = Real.sin (η * t) / t := by
      by_cases hη : η = 0
      · simp [hη]
      · rw [Real.sinc_of_ne_zero (mul_ne_zero hη hz)]
        field_simp
    rw [hs]
    push_cast
    ring

/-- Uniform central Fourier bound. -/
theorem norm_integral_centralFourier_le {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    (hs : ContDiff ℝ 1 χ) {C μ : ℝ} (hC : ∀ t, |χ t| ≤ C) (hμ : 0 < μ) (η : ℝ) :
    ‖∫ t in (-1 : ℝ)..1, (((1 - χ (μ * t)) / t : ℝ) : ℂ) * unitPhase η t‖ ≤
      6 * (1 + C + ∫ t : ℝ, |deriv χ t|) := by
  rw [integral_centralFourier_eq hχ μ η, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num
  exact (mul_le_mul_of_nonneg_left (abs_integral_cutoff_sine_le hχ hs hC hμ η)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

end WaveTurbulence
