/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleSourceCalculus
public import WaveTurbulence.Foundations.VdCB.CircleWeight

/-!
# Reciprocal source and dual curvatures for the circle

Differentiating the actual stationary equation proves the reciprocal
curvature identity. This avoids treating an asymptotic model as an exact
phase and identifies the stationary amplitude with the explicit dual weight.
-/

public section

open Set Filter
open scoped Topology

namespace WaveTurbulence.VdCB

theorem circleCriticalPoint_eq_neg_dualFirst (R : ℝ) {h : ℝ} (hh : 0 < h) (ν : ℝ) :
    circleCriticalPoint R h ν = -circleDualFirst R h ν := by
  have hD : 0 < h ^ 2 + ν ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg ν)
  unfold circleCriticalPoint circleDualFirst
  rw [Real.rpow_neg hD.le, ← Real.sqrt_eq_rpow]
  ring

theorem hasDerivAt_circleCriticalPoint (R : ℝ) {h : ℝ} (hh : 0 < h) (ν : ℝ) :
    HasDerivAt (circleCriticalPoint R h) (-circleDualSecond R h ν) ν := by
  have heq : circleCriticalPoint R h = fun x => -circleDualFirst R h x :=
    funext (circleCriticalPoint_eq_neg_dualFirst R hh)
  rw [heq]
  exact (hasDerivAt_circleDualFirst R hh ν).fun_neg

/-- Source and dual curvatures are exact positive reciprocals. -/
theorem circle_source_dual_curvature_mul {R h ν : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hν : 0 < ν) :
    (-circleSourceSecond R h (circleCriticalPoint R h ν)) * circleDualSecond R h ν = 1 := by
  have hcritical := hasDerivAt_circleCriticalPoint R hh ν
  have hcomp := (hasDerivAt_circleSourceFirst (h := h) hR (circleCriticalPoint_mem hR hh hν)).comp ν hcritical
  have heq : (circleSourceFirst R h ∘ circleCriticalPoint R h) =ᶠ[𝓝 ν] id := by
    filter_upwards [Ioi_mem_nhds hν] with x hx
    dsimp only [Function.comp_apply, id_eq]
    exact (hasDerivAt_circlePhase_rpow (h := h) hR (circleCriticalPoint_mem hR hh hx)).unique
      (hasDerivAt_circlePhase_critical hR hh hx)
  have hp := (hcomp.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id ν)
  nlinarith only [hp]

/-- Explicit expression for the square root of the dual curvature. -/
theorem sqrt_circleDualSecond {R h ν : ℝ} (hR : 0 < R) (hh : 0 < h) :
    Real.sqrt (circleDualSecond R h ν) = circleDualWeight R h ν := by
  have hD : 0 < h ^ 2 + ν ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg ν)
  have heq : Real.sqrt ((h ^ 2 + ν ^ 2) ^ (-(3 / 2) : ℝ)) =
      (h ^ 2 + ν ^ 2) ^ (-(3 / 4) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hD.le]
    norm_num
  unfold circleDualSecond circleDualWeight
  rw [Real.sqrt_mul (mul_nonneg hR.le (sq_nonneg h)), Real.sqrt_mul hR.le,
    Real.sqrt_sq_eq_abs, abs_of_pos hh, heq]

/-- The stationary amplitude equals the explicit decreasing dual weight. -/
theorem inv_sqrt_circleSourceSecond_eq_weight {R h ν : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hν : 0 < ν) :
    1 / Real.sqrt (-circleSourceSecond R h (circleCriticalPoint R h ν)) = circleDualWeight R h ν := by
  have hD : 0 < h ^ 2 + ν ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg ν)
  have hw : 0 < circleDualSecond R h ν := by unfold circleDualSecond; positivity
  have hprod := circle_source_dual_curvature_mul hR hh hν
  have hq : 0 < -circleSourceSecond R h (circleCriticalPoint R h ν) :=
    (mul_pos_iff_of_pos_right hw).mp (by rw [hprod]; norm_num)
  have hs := congrArg Real.sqrt hprod
  rw [Real.sqrt_mul hq.le, Real.sqrt_one, sqrt_circleDualSecond hR hh] at hs
  apply (div_eq_iff (Real.sqrt_pos.mpr hq).ne').mpr
  nlinarith only [hs]

end WaveTurbulence.VdCB
