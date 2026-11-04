/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.NonstationaryIdentity
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# First-derivative control of a nonstationary integral

For positive increasing phase derivative at distance at least `lam` from
zero, the normalized integral is bounded by `1/(π lam)`. This is the
continuous first-derivative estimate used for the nonstationary tails.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Quantitative first-derivative estimate with an explicit absolute constant. -/
theorem norm_integral_expPhase_le_of_deriv_pos {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hderiv : ∀ x ∈ Icc a b, lam ≤ deriv f x)
    (hsecond : ∀ x ∈ Icc a b, 0 ≤ deriv (deriv f) x) :
    ‖∫ x in a..b, expPhase (f x)‖ ≤ 1 / (Real.pi * lam) := by
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hn (x : ℝ) (hx : x ∈ Icc a b) : 0 < deriv f x := hlam.trans_le (hderiv x hx)
  let A : ℝ → ℝ := fun x => (deriv f x)⁻¹
  let A' : ℝ → ℝ := fun x => -(deriv (deriv f) x) / (deriv f x) ^ 2
  have hdA (x : ℝ) (hx : x ∈ uIcc a b) : HasDerivAt A (A' x) x := by
    rw [uIcc_of_le hab] at hx
    exact ((hf1.differentiable (by norm_num) x).hasDerivAt.inv (hn x hx).ne')
  have hAc : ContinuousOn A' (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hf1.continuous_deriv_one.continuousOn.neg.div
      (hf1.continuous.continuousOn.pow 2) (fun x hx => pow_ne_zero 2 (hn x hx).ne')
  have hAi := hAc.intervalIntegrable (μ := volume)
  have hAint : (∫ x in a..b, |A' x|) = A a - A b := by
    calc
      _ = ∫ x in a..b, -A' x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        dsimp only
        exact abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hsecond x hx)) (sq_nonneg _))
      _ = -(∫ x in a..b, A' x) := intervalIntegral.integral_neg
      _ = _ := by rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hdA hAi]; ring
  have hR : ‖∫ x in a..b, expPhase (f x) * (A' x : ℂ)‖ ≤ A a - A b := by
    have hh := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun x => expPhase (f x) * (A' x : ℂ)) hab
    simpa only [norm_mul, norm_expPhase, one_mul, Complex.norm_real, Real.norm_eq_abs, hAint] using hh
  have hA0 (x : ℝ) (hx : x ∈ Icc a b) : 0 ≤ A x := (inv_pos.mpr (hn x hx)).le
  have hbd (x : ℝ) (hx : x ∈ Icc a b) : ‖expPhase (f x) * (A x : ℂ)‖ = A x := by
    rw [norm_mul, norm_expPhase, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA0 x hx)]
  have hnum : ‖expPhase (f b) * (A b : ℂ) - expPhase (f a) * (A a : ℂ) -
      ∫ x in a..b, expPhase (f x) * (A' x : ℂ)‖ ≤ 2 * A a := by
    have hh := (norm_sub_le (expPhase (f b) * (A b : ℂ) - expPhase (f a) * (A a : ℂ))
      (∫ x in a..b, expPhase (f x) * (A' x : ℂ))).trans
        (add_le_add (norm_sub_le (expPhase (f b) * (A b : ℂ)) (expPhase (f a) * (A a : ℂ))) hR)
    rw [hbd b (right_mem_Icc.mpr hab), hbd a (left_mem_Icc.mpr hab)] at hh
    linarith only [hh]
  have heq := integral_expPhase_nonstationary hf
    (fun x hx => (hn x ((uIcc_of_le hab) ▸ hx)).ne')
  change (∫ x in a..b, expPhase (f x)) =
    (expPhase (f b) * (A b : ℂ) - expPhase (f a) * (A a : ℂ) -
      ∫ x in a..b, expPhase (f x) * (A' x : ℂ)) / ((2 * Real.pi : ℂ) * Complex.I) at heq
  have hden : ‖(2 * Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [heq, norm_div, hden]
  calc
    _ ≤ (2 * A a) / (2 * Real.pi) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = A a / Real.pi := by field_simp
    _ ≤ lam⁻¹ / Real.pi := div_le_div_of_nonneg_right (inv_anti₀ hlam (hderiv a (left_mem_Icc.mpr hab))) Real.pi_pos.le
    _ = _ := by rw [one_div, mul_inv, div_eq_mul_inv]; ring

end WaveTurbulence.VdCB
