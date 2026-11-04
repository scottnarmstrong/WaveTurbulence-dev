/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.NonstationaryIdentity
public import WaveTurbulence.Foundations.VdCB.SymmetricKernel

/-!
# Integration by parts for a Poisson frequency

At integer endpoints the frequency character equals one. The remaining
endpoint denominator is the actual phase derivative minus the frequency.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Derivative of the actual frequency-shifted phase. -/
theorem deriv_sub_frequency {f : ℝ → ℝ} (hf : Differentiable ℝ f) (ν x : ℝ) :
    deriv (fun y => f y - ν * y) x = deriv f x - ν := by
  have hh := (hf x).hasDerivAt.sub ((hasDerivAt_id x).const_mul ν)
  have heq : (f - fun y => ν * id y) = (fun y => f y - ν * y) := by
    funext y
    simp only [Pi.sub_apply, id_eq]
  rw [heq] at hh
  simpa only [mul_one] using hh.deriv

/-- Its second derivative is unchanged. -/
theorem deriv_deriv_sub_frequency {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (ν x : ℝ) :
    deriv (deriv (fun y => f y - ν * y)) x = deriv (deriv f) x := by
  rw [show deriv (fun y => f y - ν * y) = fun y => deriv f y - ν from
    funext (deriv_sub_frequency (hf.differentiable (by norm_num)) ν)]
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact ((hf1.differentiable (by norm_num) x).hasDerivAt.sub_const ν).deriv

/-- The frequency term disappears from an integer endpoint character. -/
theorem expPhase_sub_int_mul_int (f : ℝ → ℝ) (ν n : ℤ) :
    expPhase (f n - (ν : ℝ) * n) = expPhase (f n) := by
  have hh := expPhase_add_intCast (f n) (-(ν * n))
  simpa only [Int.cast_neg, Int.cast_mul, sub_eq_add_neg] using hh

/-- Exact nonstationary identity for an individual Poisson integral on
integer endpoints. Pairing frequencies is performed only after this step. -/
theorem integral_expPhase_sub_frequency {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (a b ν : ℤ) (hne : ∀ x ∈ uIcc (a : ℝ) b, deriv f x - ν ≠ 0) :
    (∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)) =
      (expPhase (f b) * (((deriv f b - ν)⁻¹ : ℝ) : ℂ) -
       expPhase (f a) * (((deriv f a - ν)⁻¹ : ℝ) : ℂ) +
       ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x) *
         ((deriv (deriv f) x / (deriv f x - ν) ^ 2 : ℝ) : ℂ)) /
           ((2 * Real.pi : ℂ) * Complex.I) := by
  have hd := hf.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hh := integral_expPhase_nonstationary
    (f := fun x => f x - (ν : ℝ) * x) (hf.sub (contDiff_const.mul contDiff_id))
    (a := (a : ℝ)) (b := (b : ℝ)) (by simpa only [deriv_sub_frequency hd] using hne)
  simp_rw [deriv_sub_frequency hd, deriv_deriv_sub_frequency hf,
    expPhase_sub_int_mul_int] at hh
  rw [hh]
  congr 1
  have hi : (∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x) *
      ((-deriv (deriv f) x / (deriv f x - ν) ^ 2 : ℝ) : ℂ)) =
      -(∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x) *
        ((deriv (deriv f) x / (deriv f x - ν) ^ 2 : ℝ) : ℂ)) := by
    simp_rw [neg_div, Complex.ofReal_neg, mul_neg]
    exact intervalIntegral.integral_neg
  rw [hi, sub_neg_eq_add]

end WaveTurbulence.VdCB
