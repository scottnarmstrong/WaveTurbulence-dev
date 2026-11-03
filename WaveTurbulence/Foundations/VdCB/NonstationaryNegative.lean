/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.NonstationaryBound

/-!
# The negative increasing-derivative convention

Reflection converts a negative increasing phase derivative into a
positive increasing derivative, preserving the normalized integral.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

theorem deriv_comp_neg {f : ℝ → ℝ} (hf : Differentiable ℝ f) (x : ℝ) :
    deriv (fun y => f (-y)) x = -deriv f (-x) := by
  have hh := ((hf (-x)).hasDerivAt.comp x ((hasDerivAt_id x).neg)).deriv
  have heq : (f ∘ Neg.neg) = (fun y => f (-y)) := by
    funext y
    simp only [Function.comp_apply]
  rw [heq] at hh
  simpa only [mul_neg, mul_one] using hh

theorem deriv_deriv_comp_neg {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    deriv (deriv (fun y => f (-y))) x = deriv (deriv f) (-x) := by
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  rw [show deriv (fun y => f (-y)) = (fun y => -deriv f (-y)) from
    funext (deriv_comp_neg (hf.differentiable (by norm_num)))]
  rw [deriv.fun_neg, deriv_comp_neg (hf1.differentiable (by norm_num)), neg_neg]

/-- First-derivative estimate for a negative increasing derivative. -/
theorem norm_integral_expPhase_le_of_deriv_neg {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hderiv : ∀ x ∈ Icc a b, deriv f x ≤ -lam)
    (hsecond : ∀ x ∈ Icc a b, 0 ≤ deriv (deriv f) x) :
    ‖∫ x in a..b, expPhase (f x)‖ ≤ 1 / (Real.pi * lam) := by
  have hd := hf.differentiable (by norm_num)
  have hg : ContDiff ℝ 2 (fun x => f (-x)) := hf.comp contDiff_id.neg
  have hh := norm_integral_expPhase_le_of_deriv_pos hg
    (a := -b) (b := -a) (neg_le_neg hab) hlam
    (fun x hx => by
      rw [deriv_comp_neg hd]
      have h := hderiv (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      linarith only [h])
    (fun x hx => by
      rw [deriv_deriv_comp_neg hf]
      exact hsecond (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  have heq := intervalIntegral.integral_comp_neg
    (f := fun x => expPhase (f x)) (a := -b) (b := -a)
  simp only [neg_neg] at heq
  rw [heq] at hh
  exact hh

end WaveTurbulence.VdCB
