/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleSourceCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Uniqueness of the actual circle critical point

The source first derivative is strictly decreasing throughout the open
arc. Any stationary point selected by intermediate value is therefore
the explicit circle critical point used by the Legendre formula.
-/

public section

open Set

namespace WaveTurbulence.VdCB

theorem strictAntiOn_circleSourceFirst {R h : ℝ} (hR : 0 < R) (hh : 0 < h) :
    StrictAntiOn (circleSourceFirst R h) (Ioo 0 R) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 R)
  · intro x hx
    exact (hasDerivAt_circleSourceFirst hR hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := (interior_subset hx : x ∈ Ioo 0 R)
    rw [(hasDerivAt_circleSourceFirst (h := h) hR hx').deriv]
    unfold circleSourceSecond
    have hD : 0 < 2 * R * x - x ^ 2 := by nlinarith only [hR, hx'.1, hx'.2]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hh) (sq_pos_of_pos hR)) (Real.rpow_pos_of_pos hD _)

/-- An actual source critical equation identifies the explicit point. -/
theorem eq_circleCriticalPoint_of_sourceFirst_eq {R h ν x : ℝ}
    (hR : 0 < R) (hh : 0 < h) (hν : 0 < ν) (hx : x ∈ Ioo 0 R)
    (hcritical : circleSourceFirst R h x = ν) : x = circleCriticalPoint R h ν := by
  apply (strictAntiOn_circleSourceFirst hR hh).injOn hx (circleCriticalPoint_mem hR hh hν)
  have hc := (hasDerivAt_circlePhase_rpow (h := h) hR (circleCriticalPoint_mem hR hh hν)).unique
    (hasDerivAt_circlePhase_critical hR hh hν)
  exact hcritical.trans hc.symm

end WaveTurbulence.VdCB
