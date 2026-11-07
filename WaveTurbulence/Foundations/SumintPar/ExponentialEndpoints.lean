/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.PairKernels
public import WaveTurbulence.Foundations.Fourier.TimeWeights
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Exact Fourier endpoints for the explicit sumint time extension

Exponential weights make the interval and half-line Fourier integrals
exact rational endpoint expressions. Their denominators never vanish,
so no separate low-frequency convention or remainder is needed.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- The complex rate of an exponential weight times a negative Fourier character. -/
@[expose] noncomputable def exponentialRate (σ ξ : ℝ) : ℂ :=
  (σ : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I

/-- Exact combination of the real exponential and the Fourier character. -/
theorem exponential_mul_char (σ ξ t : ℝ) :
    (Real.exp (σ*t) : ℂ) * (Real.fourierChar (-ξ*t) : ℂ) =
      Complex.exp (exponentialRate σ ξ * t) := by
  rw [Real.fourierChar_apply, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  unfold exponentialRate
  push_cast
  ring

/-- The real part of the rate is exactly the chosen weight. -/
theorem exponentialRate_re (σ ξ : ℝ) : (exponentialRate σ ξ).re = σ := by
  simp [exponentialRate]

/-- A nonzero real exponential weight gives a nonzero Fourier denominator. -/
theorem exponentialRate_ne_zero {σ : ℝ} (hσ : σ ≠ 0) (ξ : ℝ) : exponentialRate σ ξ ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  exact hσ (by simpa only [exponentialRate_re, Complex.zero_re] using hh)

/-- Exact closed-interval endpoint formula with the decaying positive-time weight. -/
theorem integral_exp_neg_char_Icc {a b : ℝ} (hab : a ≤ b) (ξ : ℝ) :
    (∫ t in Icc a b, (Real.exp (-t) : ℂ) * (Real.fourierChar (-ξ*t) : ℂ)) =
      (Complex.exp (exponentialRate (-1) ξ * b) -
        Complex.exp (exponentialRate (-1) ξ * a)) / exponentialRate (-1) ξ := by
  have he (t : ℝ) : (Real.exp (-t) : ℂ) * (Real.fourierChar (-ξ*t) : ℂ) =
      Complex.exp (exponentialRate (-1) ξ * t) := by simpa only [neg_one_mul] using exponential_mul_char (-1) ξ t
  simp_rw [he]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_exp_mul_complex (exponentialRate_ne_zero (by norm_num) ξ)]

/-- Exact strict-half-line formula with the decaying negative-time weight. -/
theorem integral_exp_pos_char_Iio (u ξ : ℝ) :
    (∫ t in Iio u, (Real.exp t : ℂ) * (Real.fourierChar (-ξ*t) : ℂ)) =
      Complex.exp (exponentialRate 1 ξ * u) / exponentialRate 1 ξ := by
  have he (t : ℝ) : (Real.exp t : ℂ) * (Real.fourierChar (-ξ*t) : ℂ) =
      Complex.exp (exponentialRate 1 ξ * t) := by simpa only [one_mul] using exponential_mul_char 1 ξ t
  simp_rw [he]
  rw [← integral_Iic_eq_integral_Iio,
    integral_exp_mul_complex_Iic (by simp only [exponentialRate_re]; norm_num)]

end WaveTurbulence.SumintPar
