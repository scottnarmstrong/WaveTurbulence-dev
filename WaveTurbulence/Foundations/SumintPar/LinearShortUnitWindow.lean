/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.WindowRescale
public import WaveTurbulence.Foundations.LemLin.LinearWindow
import Mathlib.Tactic

/-!
# Linear factors with an arbitrary positive time scale

Only the genuine short-window condition is needed. This avoids imposing
a spurious source momentum upper bound after the width-four cutoff is
rescaled to a width-one cutoff at mesh parameter `4L`.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- The cancellation branch on a unit time interval at any positive scale. -/
theorem linear_short_unit_window {d : ℕ} {L c : ℝ} (hL : 1 ≤ L) (hc : 0 < c)
    (a r ξ : Mom d) (hr : r ≠ 0) (hshort : c * ‖r‖ ≤ L) (q t : ℝ) :
    (∫ s in Icc q (q+1), ‖LemLin.linearLatticeSum L a ((c*(s-t)) • r+ξ)‖) ≤
      c⁻¹ * (LemLin.linearCancellationConstant d * L^d / ‖r‖) := by
  rw [integral_unit_affine (fun u => ‖LemLin.linearLatticeSum L a (u • r+ξ)‖) hc]
  exact mul_le_mul_of_nonneg_left
    (LemLin.integral_linear_flow_cancellation hL hc.le a r ξ hr hshort (c*(q-t)))
    (inv_nonneg.mpr hc.le)

/-- The trivial branch is independent of the time scale and output momentum. -/
theorem linear_trivial_unit_window {d : ℕ} {L c : ℝ} (hL : 1 ≤ L) (hc : 0 < c)
    (a r ξ : Mom d) (q t : ℝ) :
    (∫ s in Icc q (q+1), ‖LemLin.linearLatticeSum L a ((c*(s-t)) • r+ξ)‖) ≤
      (3:ℝ)^d * L^d := by
  rw [integral_unit_affine (fun u => ‖LemLin.linearLatticeSum L a (u • r+ξ)‖) hc]
  exact (mul_le_mul_of_nonneg_left
    (LemLin.integral_linear_flow_trivial hL hc.le a r ξ (c*(q-t)))
    (inv_nonneg.mpr hc.le)).trans_eq (by field_simp)

end WaveTurbulence.SumintPar
