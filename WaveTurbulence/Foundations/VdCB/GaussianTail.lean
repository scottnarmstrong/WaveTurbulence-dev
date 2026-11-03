/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.QuadraticTail
public import WaveTurbulence.Foundations.VdCB.MonotoneAmplitude
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Uniform damped Fresnel tails

Gaussian damping does not enlarge the inverse-distance tail estimate.
The reciprocal amplitude is positive and decreasing, uniformly as the
damping parameter tends to zero.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Uniform tail bound for Gaussian-damped quadratic oscillations. -/
theorem norm_integral_damped_quadratic_tail_le {q ε a b : ℝ}
    (hq : 0 < q) (hε : 0 ≤ ε) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, expPhase (q * x ^ 2 / 2) *
      (Real.exp (-Real.pi * ε * x ^ 2) : ℂ)‖ ≤ 1 / (Real.pi * (q * a)) := by
  let A : ℝ → ℝ := fun x => Real.exp (-Real.pi * ε * x ^ 2) / (q * x)
  let A' : ℝ → ℝ := fun x =>
    (((-Real.pi * ε * (2 * x)) * Real.exp (-Real.pi * ε * x ^ 2)) * (q * x) -
      Real.exp (-Real.pi * ε * x ^ 2) * q) / (q * x) ^ 2
  have hxpos (x : ℝ) (hx : x ∈ uIcc a b) : 0 < x := by
    rw [uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hd (x : ℝ) (hx : x ∈ uIcc a b) : HasDerivAt A (A' x) x := by
    have hp0 : HasDerivAt (fun y : ℝ => -Real.pi * ε * y ^ 2)
        (-Real.pi * ε * (2 * x)) x := by
      simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using
        (((hasDerivAt_id x).pow 2).const_mul (-Real.pi * ε))
    have hp := hp0.exp
    have hh := hp.div ((hasDerivAt_id x).const_mul q) (mul_pos hq (hxpos x hx)).ne'
    convert hh using 1
    · funext y
      simp only [A, Pi.div_apply, id_eq]
    · dsimp only [A', Pi.pow_apply, id_eq]
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      ring
  have hc : ContinuousOn A' (uIcc a b) := by
    dsimp only [A']
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      exact pow_ne_zero 2 (mul_pos hq (hxpos x hx)).ne'
  have hApos (x : ℝ) (hx : x ∈ uIcc a b) : 0 ≤ A x := by
    exact div_nonneg (Real.exp_pos _).le (mul_pos hq (hxpos x hx)).le
  have hneg (x : ℝ) (hx : x ∈ Icc a b) : A' x ≤ 0 := by
    have hx0 : 0 < x := ha.trans_le hx.1
    dsimp only [A']
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have ht : -Real.pi * ε * (2 * x) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) hε) (by positivity)
    have hh := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg ht (Real.exp_pos (-Real.pi * ε * x ^ 2)).le) (mul_pos hq hx0).le
    exact sub_nonpos.mpr (hh.trans (mul_nonneg (Real.exp_pos _).le hq.le))
  have hh := norm_integral_phase_deriv_amplitude_le
    (f := fun x => q * x ^ 2 / 2) (by fun_prop) hab hd hc
    (hApos a (left_mem_uIcc)) (hApos b (right_mem_uIcc)) hneg
  have heq : (∫ x in a..b, expPhase (q * x ^ 2 / 2) *
      ((deriv (fun y : ℝ => q * y ^ 2 / 2) x : ℝ) : ℂ) * (A x : ℂ)) =
      ∫ x in a..b, expPhase (q * x ^ 2 / 2) * (Real.exp (-Real.pi * ε * x ^ 2) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [deriv_quadratic_phase]
    dsimp only [A]
    rw [mul_assoc, ← Complex.ofReal_mul, mul_div_cancel₀ _ (mul_pos hq (hxpos x hx)).ne']
  rw [heq] at hh
  apply hh.trans
  have hExp : Real.exp (-Real.pi * ε * a ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) hε) (sq_nonneg a)
  calc
    A a / Real.pi ≤ (1 / (q * a)) / Real.pi :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hExp (mul_pos hq ha).le) Real.pi_pos.le
    _ = _ := by ring

end WaveTurbulence.VdCB
