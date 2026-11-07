/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ExponentialEndpoints
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Uniform Fourier bounds for exponential endpoint factors

On nonnegative finite intervals and negative half-lines the exponential
endpoint numerators have modulus at most two and one, respectively.
Both nonvanishing denominators dominate the scalar Japanese bracket.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- Both signs of the exponential rate dominate the scalar Fourier bracket. -/
theorem scalarBracket_le_norm_exponentialRate {σ : ℝ} (hσ : σ^2 = 1) (ξ : ℝ) :
    scalarBracket ξ ≤ ‖exponentialRate σ ξ‖ := by
  have hre := exponentialRate_re σ ξ
  have him : (exponentialRate σ ξ).im = -(2 * Real.pi * ξ) := by simp [exponentialRate]
  rw [Complex.norm_def, Complex.normSq_apply, hre, him, ← sq, neg_mul_neg, ← sq, hσ]
  unfold scalarBracket
  apply Real.sqrt_le_sqrt
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have ha : |ξ| ≤ |2 * Real.pi * ξ| := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 2 * Real.pi)]
    exact le_mul_of_one_le_left (abs_nonneg _) hpi
  have hsq : ξ^2 ≤ (2 * Real.pi * ξ)^2 := sq_le_sq.mpr ha
  linarith only [hsq]

/-- A strict negative half-line gives one inverse bracket. -/
theorem norm_integral_exp_pos_char_Iio_le {u : ℝ} (hu : u ≤ 0) (ξ : ℝ) :
    ‖∫ t in Iio u, (Real.exp t : ℂ) * (Real.fourierChar (-ξ*t) : ℂ)‖ ≤
      1 / scalarBracket ξ := by
  rw [integral_exp_pos_char_Iio, norm_div, Complex.norm_exp]
  have he : (exponentialRate 1 ξ * (u : ℂ)).re = u := by simp [Complex.mul_re, exponentialRate_re]
  rw [he]
  have hr := scalarBracket_le_norm_exponentialRate (σ := 1) (by norm_num) ξ
  calc
    _ ≤ 1 / ‖exponentialRate 1 ξ‖ :=
      div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr hu) (norm_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (lt_of_lt_of_le zero_lt_one (one_le_scalarBracket ξ)) hr

/-- A nonnegative finite interval gives two inverse brackets, uniformly in both endpoints. -/
theorem norm_integral_exp_neg_char_Icc_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ξ : ℝ) :
    ‖∫ t in Icc a b, (Real.exp (-t) : ℂ) * (Real.fourierChar (-ξ*t) : ℂ)‖ ≤
      2 / scalarBracket ξ := by
  rw [integral_exp_neg_char_Icc hab, norm_div]
  have he (v : ℝ) : (exponentialRate (-1) ξ * (v : ℂ)).re = -v := by
    simp [Complex.mul_re, exponentialRate_re]
  have hnum : ‖Complex.exp (exponentialRate (-1) ξ * (b : ℂ)) -
      Complex.exp (exponentialRate (-1) ξ * (a : ℂ))‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    rw [Complex.norm_exp, Complex.norm_exp, he, he]
    have hb := Real.exp_le_one_iff.mpr (show -b ≤ 0 by linarith)
    have ha' := Real.exp_le_one_iff.mpr (show -a ≤ 0 by linarith)
    linarith
  have hr := scalarBracket_le_norm_exponentialRate (σ := -1) (by norm_num) ξ
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by norm_num) (lt_of_lt_of_le zero_lt_one (one_le_scalarBracket ξ)) hr)

end WaveTurbulence.SumintPar
