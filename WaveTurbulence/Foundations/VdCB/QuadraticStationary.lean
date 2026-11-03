/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.FresnelCoefficient

/-!
# Quantitative quadratic stationary phase

The first error term is controlled by the second Fourier moment of the
amplitude. It follows from the exact quadratic identity and the Lipschitz
bound for the normalized character.
-/

public section

open MeasureTheory
open WaveTurbulence.NumberTheory
open scoped FourierTransform SchwartzMap

namespace WaveTurbulence.VdCB

/-- Fourier inversion at the critical point. -/
theorem integral_fourier_schwartz_eq_zero_value (a : 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, 𝓕 a ξ) = a 0 := by
  have hh := congrArg (fun b : 𝓢(ℝ, ℂ) => b 0) (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) a)
  rw [SchwartzMap.fourierInv_coe] at hh
  simpa [Real.fourierInv_eq] using hh

/-- Explicit quadratic stationary-phase error in terms of the Fourier
second moment. This estimate is uniform over every Schwartz amplitude. -/
theorem norm_integral_schwartz_mul_quadratic_sub_le (a : 𝓢(ℝ, ℂ)) {q : ℝ} (hq : 0 < q) :
    ‖(∫ x : ℝ, a x * expPhase (q * x ^ 2 / 2)) -
      (expPhase (1 / 8) / (Real.sqrt q : ℂ)) * ∫ ξ : ℝ, 𝓕 a ξ‖ ≤
      (1 / Real.sqrt q) * (Real.pi / q) * ∫ ξ : ℝ, ‖ξ‖ ^ 2 * ‖𝓕 a ξ‖ := by
  have hnorm : ‖expPhase (1 / 8) / (Real.sqrt q : ℂ)‖ = 1 / Real.sqrt q := by
    rw [norm_div, norm_expPhase, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg q)]
  have hbound (ξ : ℝ) :
      ‖𝓕 a ξ * (expPhase (-(ξ ^ 2) / (2 * q)) - 1)‖ ≤
        (Real.pi / q) * (‖ξ‖ ^ 2 * ‖𝓕 a ξ‖) := by
    rw [norm_mul]
    have hp := norm_expPhase_sub_le (-(ξ ^ 2) / (2 * q)) 0
    rw [expPhase_zero, sub_zero, abs_div, abs_neg, abs_of_nonneg (sq_nonneg ξ),
      abs_of_pos (by positivity : 0 < 2 * q)] at hp
    have he : 2 * Real.pi * (ξ ^ 2 / (2 * q)) = (Real.pi / q) * ‖ξ‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
      field_simp
    rw [he] at hp
    calc
      _ ≤ ‖𝓕 a ξ‖ * ((Real.pi / q) * ‖ξ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = _ := by ring
  have hi := ((𝓕 a).integrable_pow_mul volume 2).const_mul (Real.pi / q)
  have hosc : Integrable (fun ξ : ℝ => 𝓕 a ξ * expPhase (-(ξ ^ 2) / (2 * q))) := by
    have hc : Continuous (fun ξ : ℝ => 𝓕 a ξ * expPhase (-(ξ ^ 2) / (2 * q))) :=
      (𝓕 a).continuous.mul ((contDiff_expPhase 0).continuous.comp (by fun_prop))
    apply ((𝓕 a).integrable (μ := volume)).norm.mono' hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ξ => by rw [norm_mul, norm_expPhase, mul_one]
  rw [integral_schwartz_mul_quadratic a hq, ← mul_sub, ← integral_sub hosc (𝓕 a).integrable]
  simp_rw [show ∀ ξ : ℝ, 𝓕 a ξ * expPhase (-(ξ ^ 2) / (2 * q)) - 𝓕 a ξ =
    𝓕 a ξ * (expPhase (-(ξ ^ 2) / (2 * q)) - 1) from fun ξ => by ring]
  rw [norm_mul, hnorm]
  calc
    _ ≤ (1 / Real.sqrt q) * ∫ ξ : ℝ, (Real.pi / q) * (‖ξ‖ ^ 2 * ‖𝓕 a ξ‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hbound)) (by positivity)
    _ = _ := by rw [integral_const_mul]; ring

/-- Quadratic stationary phase with the amplitude evaluated at its actual
critical point and an explicit Fourier-moment error. -/
theorem norm_integral_schwartz_mul_quadratic_sub_main_le (a : 𝓢(ℝ, ℂ)) {q : ℝ} (hq : 0 < q) :
    ‖(∫ x : ℝ, a x * expPhase (q * x ^ 2 / 2)) -
      (expPhase (1 / 8) / (Real.sqrt q : ℂ)) * a 0‖ ≤
      (1 / Real.sqrt q) * (Real.pi / q) * ∫ ξ : ℝ, ‖ξ‖ ^ 2 * ‖𝓕 a ξ‖ := by
  simpa only [integral_fourier_schwartz_eq_zero_value] using
    norm_integral_schwartz_mul_quadratic_sub_le a hq

end WaveTurbulence.VdCB
