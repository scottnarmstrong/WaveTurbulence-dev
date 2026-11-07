/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.WindowRescaleGeneral
public import WaveTurbulence.Foundations.LemLin.LinearWindow
import Mathlib.Tactic

/-!
# Linear cancellation on the enlarged source intervals

The local time partition enlarges unit intervals. We keep their actual
length, and impose precisely the landed short-window condition on the
rescaled length. The trivial estimate retains the interval length too.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- Linear cancellation on an arbitrary ordered affine window. -/
theorem linear_short_window {d : ℕ} {L c a b : ℝ} (hL : 1 ≤ L) (hc : 0 < c)
    (hab : a ≤ b) (p r ξ : Mom d) (hr : r ≠ 0)
    (hshort : (c*(b-a))*‖r‖ ≤ L) (t : ℝ) :
    (∫ s in Icc a b, ‖LemLin.linearLatticeSum L p ((c*(s-t)) • r+ξ)‖) ≤
      c⁻¹ * (LemLin.linearCancellationConstant d * L^d / ‖r‖) := by
  rw [integral_Icc_affine (fun u => ‖LemLin.linearLatticeSum L p (u • r+ξ)‖) hc hab]
  have he : c*(b-t) = c*(a-t)+c*(b-a) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_left
    (LemLin.integral_linear_flow_cancellation hL (mul_nonneg hc.le (sub_nonneg.mpr hab))
      p r ξ hr hshort (c*(a-t))) (inv_nonneg.mpr hc.le)

/-- The trivial bound on the same window retains its exact length. -/
theorem linear_trivial_window {d : ℕ} {L c a b : ℝ} (hL : 1 ≤ L) (hc : 0 < c)
    (hab : a ≤ b) (p r ξ : Mom d) (t : ℝ) :
    (∫ s in Icc a b, ‖LemLin.linearLatticeSum L p ((c*(s-t)) • r+ξ)‖) ≤
      (b-a) * (3:ℝ)^d * L^d := by
  rw [integral_Icc_affine (fun u => ‖LemLin.linearLatticeSum L p (u • r+ξ)‖) hc hab]
  have he : c*(b-t) = c*(a-t)+c*(b-a) := by ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left
    (LemLin.integral_linear_flow_trivial hL (mul_nonneg hc.le (sub_nonneg.mpr hab))
      p r ξ (c*(a-t))) (inv_nonneg.mpr hc.le)).trans_eq (by field_simp)

end WaveTurbulence.SumintPar
