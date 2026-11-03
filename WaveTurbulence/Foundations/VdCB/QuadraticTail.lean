/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.NonstationaryBound
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Quadratic Fresnel tails

The positive half-line away from the critical point is controlled by the
continuous first-derivative estimate. The bound is uniform in the upper
endpoint, so it is suitable for a later improper-integral limit.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Actual first derivative of the normalized quadratic phase. -/
theorem deriv_quadratic_phase (q x : ℝ) :
    deriv (fun y : ℝ => q * y ^ 2 / 2) x = q * x := by
  have hh := (((hasDerivAt_id x).pow 2).const_mul q).div_const 2
  simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one,
    show ∀ y : ℝ, q * (2 * y) / 2 = q * y from fun y => by ring] using hh.deriv

/-- Actual second derivative of the normalized quadratic phase. -/
theorem deriv_deriv_quadratic_phase (q x : ℝ) :
    deriv (deriv (fun y : ℝ => q * y ^ 2 / 2)) x = q := by
  have heq : deriv (fun y : ℝ => q * y ^ 2 / 2) = fun y => q * y :=
    funext (deriv_quadratic_phase q)
  rw [heq]
  simpa only [mul_one, id_eq] using ((hasDerivAt_id x).const_mul q).deriv

/-- The sharp quadratic tail has a uniform inverse-distance bound. -/
theorem norm_integral_quadratic_tail_le {q a b : ℝ} (hq : 0 < q) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, expPhase (q * x ^ 2 / 2)‖ ≤ 1 / (Real.pi * (q * a)) := by
  apply norm_integral_expPhase_le_of_deriv_pos (by fun_prop) hab (mul_pos hq ha)
  · intro x hx
    rw [deriv_quadratic_phase]
    exact mul_le_mul_of_nonneg_left hx.1 hq.le
  · intro x _
    rw [deriv_deriv_quadratic_phase]
    exact hq.le

end WaveTurbulence.VdCB
