/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.PhaseCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Reflection and conjugation for the circle column phase

The endpoint-distance variable is an affine reflection of the original
column. Negating the phase makes its curvature positive. These exact
calculus identities retain the arbitrary real translation.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Derivative under an affine reflection. -/
theorem deriv_comp_sub_const {f : ℝ → ℝ} (hf : Differentiable ℝ f) (D x : ℝ) :
    deriv (fun y => f (D-y)) x = -deriv f (D-x) := by
  have hh := (hf (D-x)).hasDerivAt.comp x ((hasDerivAt_id x).const_sub D)
  have he : (f ∘ HSub.hSub D) = (fun y => f (D-y)) := by funext y; rfl
  have hd := hh.deriv
  rw [he] at hd
  simpa only [one_mul,neg_mul,mul_one,mul_neg] using hd

/-- Negating the reflected phase cancels the sign in its first derivative. -/
theorem deriv_neg_comp_sub_const {f : ℝ → ℝ} (hf : Differentiable ℝ f) (D x : ℝ) :
    deriv (fun y => -f (D-y)) x = deriv f (D-x) := by
  rw [deriv.fun_neg,deriv_comp_sub_const hf,neg_neg]

/-- The reflected negative phase has the opposite second derivative. -/
theorem deriv_deriv_neg_comp_sub_const {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (D x : ℝ) :
    deriv (deriv (fun y => -f (D-y))) x = -deriv (deriv f) (D-x) := by
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  rw [show deriv (fun y => -f (D-y)) = (fun y => deriv f (D-y)) from
    funext (deriv_neg_comp_sub_const (hf.differentiable (by norm_num)) D)]
  exact deriv_comp_sub_const (hf1.differentiable (by norm_num)) D x

/-- The third derivative returns to the original sign. -/
theorem iteratedDeriv_three_neg_comp_sub_const {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (D x : ℝ) :
    iteratedDeriv 3 (fun y => -f (D-y)) x = iteratedDeriv 3 f (D-x) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hfd : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have hfdd : ContDiff ℝ 1 (deriv (deriv f)) := hfd.deriv'
  have heq : deriv (deriv (fun y => -f (D-y))) =
      (fun y => -deriv (deriv f) (D-y)) := funext (deriv_deriv_neg_comp_sub_const hf2 D)
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [heq,deriv_neg_comp_sub_const (hfdd.differentiable (by norm_num))]

/-- Negating a real phase preserves the norm of its actual finite sum. -/
theorem norm_sum_expPhase_neg {α : Type*} (s : Finset α) (f : α → ℝ) :
    ‖∑ x ∈ s, expPhase (-f x)‖ = ‖∑ x ∈ s, expPhase (f x)‖ := by
  have heq : (∑ x ∈ s, expPhase (-f x)) = starRingEnd ℂ (∑ x ∈ s, expPhase (f x)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    exact (conj_expPhase (f x)).symm
  rw [heq]
  exact RCLike.norm_conj _

end WaveTurbulence.NumberTheory
