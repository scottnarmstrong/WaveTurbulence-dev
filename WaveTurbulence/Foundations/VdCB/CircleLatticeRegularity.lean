/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleLatticeDual
public import WaveTurbulence.Foundations.VdCB.DerivativeClass

/-!
# Smoothness and source-interval derivatives of the circle dual

The original integer-column dual includes a linear term relative to the
small decreasing-power phase. A fifth-derivative test ignores that term.
This file exposes smoothness and the actual relative fifth-derivative
bounds needed by the A-process side, without a false first-derivative
profile assertion for the full lattice dual.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.VdCB

theorem contDiff_circleDualPhase (R : ℝ) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ ∞ (circleDualPhase R h) := by
  have hc : ContDiff ℝ ∞ (fun x : ℝ => h ^ 2 + x ^ 2) := contDiff_const.add (contDiff_id.pow 2)
  have hn (x : ℝ) : h ^ 2 + x ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg x)).ne'
  unfold circleDualPhase
  exact (contDiff_const.mul (hc.rpow_const_of_ne hn)).sub (contDiff_const.mul contDiff_id)

theorem contDiff_circleLatticeDualPhase (R : ℝ) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ ∞ (circleLatticeDualPhase R h) := by
  unfold circleLatticeDualPhase
  exact (contDiff_circleDualPhase R hh).add (contDiff_const.mul contDiff_id)

/-- The full circle dual satisfies the required fifth-derivative scale
on its actual dyadic interval, including both endpoints. -/
theorem abs_iteratedDerivWithin_five_circleLatticeDualPhase_bounds {R h Y x : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hY : h ≤ Y) (hx : x ∈ Set.Icc Y (2 * Y)) :
    R * h ^ 2 / (125 * Y ^ 6) ≤
        |iteratedDerivWithin 5 (circleLatticeDualPhase R h) (Set.Icc Y (2 * Y)) x| ∧
      |iteratedDerivWithin 5 (circleLatticeDualPhase R h) (Set.Icc Y (2 * Y)) x| ≤
        480 * R * h ^ 2 / Y ^ 6 := by
  have hY0 := hh.trans_le hY
  have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 5)
    (uniqueDiffOn_Icc (by linarith : Y < 2 * Y))
    ((contDiff_circleLatticeDualPhase R hh).contDiffAt.of_le (by simp)) hx
  rw [heq]
  exact abs_iteratedDeriv_five_circleLatticeDualPhase_bounds hR hh hY hx

end WaveTurbulence.VdCB
