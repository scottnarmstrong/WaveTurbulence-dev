/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.Phase
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Oscillatory integration by parts

The normalized derivative factor is `2πi`. This identity is used for
nonstationary tails in truncated Poisson summation and stationary phase.
All hypotheses below are ordinary differentiation and integrability data.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Oscillatory integration by parts on a finite interval, with a real
amplitude and its actual derivative. -/
theorem integral_expPhase_mul_deriv_mul {f f' A A' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hA : ∀ x ∈ uIcc a b, HasDerivAt A (A' x) x)
    (hfi : ContinuousOn f' (uIcc a b)) (hAi : ContinuousOn A' (uIcc a b)) :
    (∫ x in a..b, expPhase (f x) * (f' x : ℂ) * (A x : ℂ)) =
      (expPhase (f b) * (A b : ℂ) - expPhase (f a) * (A a : ℂ) -
        ∫ x in a..b, expPhase (f x) * (A' x : ℂ)) / ((2 * Real.pi : ℂ) * Complex.I) := by
  have hc : ContinuousOn (fun x => expPhase (f x)) (uIcc a b) :=
    fun x hx => (hasDerivAt_expPhase_comp (hf x hx)).continuousAt.continuousWithinAt
  have hAc : ContinuousOn (fun x => (A x : ℂ)) (uIcc a b) :=
    fun x hx => (hA x hx).ofReal_comp.continuousAt.continuousWithinAt
  have hA'i : IntervalIntegrable (fun x => (A' x : ℂ)) volume a b :=
    (Complex.ofRealCLM.continuous.comp_continuousOn hAi).intervalIntegrable
  have hf'i : IntervalIntegrable (fun x => ((2 * Real.pi : ℂ) * Complex.I * (f' x : ℂ)) *
      expPhase (f x)) volume a b := by
    exact (((Complex.ofRealCLM.continuous.comp_continuousOn hfi).const_mul _).mul hc).intervalIntegrable
  have hh := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hc hAc
    (fun x hx => hasDerivAt_expPhase_comp (hf x (Ioo_subset_Icc_self hx)))
    (fun x hx => (hA x (Ioo_subset_Icc_self hx)).ofReal_comp) hf'i hA'i
  have hi1 := (hf'i.mul_continuousOn hAc)
  have hi2 := hA'i.continuousOn_mul hc
  rw [intervalIntegral.integral_add hi1 hi2] at hh
  have hi : ((2 * Real.pi : ℂ) * Complex.I) *
      (∫ x in a..b, expPhase (f x) * (f' x : ℂ) * (A x : ℂ)) +
        (∫ x in a..b, expPhase (f x) * (A' x : ℂ)) =
      expPhase (f b) * (A b : ℂ) - expPhase (f a) * (A a : ℂ) := by
    convert hh using 1
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  have hn : (2 * Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  apply (eq_div_iff hn).mpr
  linear_combination hi

end WaveTurbulence.VdCB
