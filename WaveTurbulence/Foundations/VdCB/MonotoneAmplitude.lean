/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Oscillatory integration with a decreasing positive reciprocal amplitude

The amplitude in this lemma is the factor multiplying the phase derivative.
For Gaussian damping of a quadratic phase it is `exp(-πεx²)/(qx)`.
Its monotonicity gives a uniform tail bound independent of the damping.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Integration by parts with total variation supplied by an actual
nonpositive amplitude derivative. No oscillatory estimate is assumed. -/
theorem norm_integral_phase_deriv_amplitude_le {f A A' : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {a b : ℝ} (hab : a ≤ b)
    (hA : ∀ x ∈ uIcc a b, HasDerivAt A (A' x) x)
    (hAc : ContinuousOn A' (uIcc a b))
    (hAa : 0 ≤ A a) (hAb : 0 ≤ A b) (hAneg : ∀ x ∈ Icc a b, A' x ≤ 0) :
    ‖∫ x in a..b, expPhase (f x) * ((deriv f x : ℝ) : ℂ) * (A x : ℂ)‖ ≤ A a / Real.pi := by
  have hAi := hAc.intervalIntegrable (μ := volume)
  have hi : (∫ x in a..b, |A' x|) = A a - A b := by
    calc
      _ = ∫ x in a..b, -A' x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        exact abs_of_nonpos (hAneg x hx)
      _ = -(∫ x in a..b, A' x) := intervalIntegral.integral_neg
      _ = _ := by rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hA hAi]; ring
  have hR : ‖∫ x in a..b, expPhase (f x) * (A' x : ℂ)‖ ≤ A a - A b := by
    have hh := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun x => expPhase (f x) * (A' x : ℂ)) hab
    simpa only [norm_mul, norm_expPhase, one_mul, Complex.norm_real, Real.norm_eq_abs, hi] using hh
  have heq := integral_expPhase_mul_deriv_mul
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt) hA
    hf.continuous_deriv_one.continuousOn hAc
  have hnum : ‖expPhase (f b) * (A b : ℂ) - expPhase (f a) * (A a : ℂ) -
      ∫ x in a..b, expPhase (f x) * (A' x : ℂ)‖ ≤ 2 * A a := by
    have hh := (norm_sub_le (expPhase (f b) * (A b : ℂ) - expPhase (f a) * (A a : ℂ))
      (∫ x in a..b, expPhase (f x) * (A' x : ℂ))).trans
        (add_le_add (norm_sub_le (expPhase (f b) * (A b : ℂ)) (expPhase (f a) * (A a : ℂ))) hR)
    simp only [norm_mul, norm_expPhase, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hAa, abs_of_nonneg hAb] at hh
    linarith only [hh]
  have hden : ‖(2 * Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [heq, norm_div, hden]
  calc
    _ ≤ 2 * A a / (2 * Real.pi) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by field_simp

end WaveTurbulence.VdCB
