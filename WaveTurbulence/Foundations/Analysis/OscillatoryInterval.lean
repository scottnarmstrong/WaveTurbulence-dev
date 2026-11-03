/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Oscillatory integration on short intervals

The one-node estimate used in DH21 Lemma 10.2 (L2432–2451). The Japanese
bracket is written explicitly, and the constant is uniform in both endpoints.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Analysis

/-- The reciprocal Japanese bracket on the frequency line. -/
@[expose] noncomputable def oscillatoryWeight (a : ℝ) : ℝ := (Real.sqrt (1 + a ^ 2))⁻¹

/-- The trivial length bound for an oscillatory integral. -/
theorem norm_integral_exp_I_le_length (a b q : ℝ) (hab : a ≤ b) :
    ‖∫ t in a..b, Complex.exp ((q * t : ℝ) * Complex.I)‖ ≤ b - a := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := 1)
    (fun t _ => (Complex.norm_exp_ofReal_mul_I (q * t)).le)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab), one_mul] using hh

/-- Integration of a nonzero frequency gains its reciprocal. -/
theorem norm_integral_exp_I_le_inv (a b q : ℝ) (hq : q ≠ 0) :
    ‖∫ t in a..b, Complex.exp ((q * t : ℝ) * Complex.I)‖ ≤ 2 / |q| := by
  have hqC : (q : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hq) Complex.I_ne_zero
  have heq : (fun t : ℝ => Complex.exp ((q * t : ℝ) * Complex.I)) =
      (fun t : ℝ => Complex.exp (((q : ℂ) * Complex.I) * t)) := by
    funext t
    congr 1
    push_cast
    ring
  rw [heq, integral_exp_mul_complex hqC, norm_div]
  have hn (t : ℝ) : ‖Complex.exp (((q : ℂ) * Complex.I) * t)‖ = 1 := by
    have harg : ((q : ℂ) * Complex.I) * t = (q * t : ℝ) * Complex.I := by push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have hnum := norm_sub_le (Complex.exp (((q : ℂ) * Complex.I) * b))
    (Complex.exp (((q : ℂ) * Complex.I) * a))
  rw [hn, hn] at hnum
  have hden : ‖(q : ℂ) * Complex.I‖ = |q| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  rw [hden]
  exact div_le_div_of_nonneg_right (by norm_num at hnum ⊢; exact hnum) (abs_nonneg q)

/-- A short oscillatory integral is bounded by a fixed constant times the
reciprocal Japanese bracket, including zero frequency. -/
theorem norm_integral_exp_I_le_weight {a b q : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 1) :
    ‖∫ t in a..b, Complex.exp ((q * t : ℝ) * Complex.I)‖ ≤ 4 * oscillatoryWeight q := by
  have hs : 0 < Real.sqrt (1 + q ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 + q ^ 2 by positivity)
  by_cases hq : |q| ≤ 1
  · have hsq : q ^ 2 ≤ 1 := by nlinarith only [sq_abs q, sq_le_sq₀ (abs_nonneg q) zero_le_one |>.mpr hq]
    have hsle : Real.sqrt (1 + q ^ 2) ≤ 4 := by nlinarith only [hs2, hs.le, hsq]
    have he : (1 : ℝ) ≤ 4 * oscillatoryWeight q := by
      rw [oscillatoryWeight, ← div_eq_mul_inv]
      exact (le_div_iff₀ hs).mpr (by simpa only [one_mul] using hsle)
    exact (norm_integral_exp_I_le_length a b q hab).trans (hlen.trans he)
  · have hqpos : 0 < |q| := lt_trans zero_lt_one (lt_of_not_ge hq)
    have hq0 : q ≠ 0 := abs_pos.mp hqpos
    have hsle : Real.sqrt (1 + q ^ 2) ≤ 2 * |q| := by
      have hq1 : 1 ≤ q ^ 2 := by nlinarith only [sq_abs q, lt_of_not_ge hq]
      nlinarith only [hs2, hs.le, hq1, sq_abs q, hqpos]
    have he : 2 / |q| ≤ 4 * oscillatoryWeight q := by
      rw [oscillatoryWeight, ← div_eq_mul_inv]
      apply (div_le_div_iff₀ hqpos hs).mpr
      linarith only [hsle]
    exact (norm_integral_exp_I_le_inv a b q hq0).trans he

end WaveTurbulence.Analysis
