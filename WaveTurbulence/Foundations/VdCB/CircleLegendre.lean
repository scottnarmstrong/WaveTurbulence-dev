/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleDualCalculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The exact Legendre transform of the octant circle phase

The actual phase is `h sqrt(2Ru-u²)`. Its critical point for frequency `ν`
and its Legendre value are explicit. These identities connect the direct
circle-family derivative estimates to the original oscillatory integrals.
-/

public section

namespace WaveTurbulence.VdCB

/-- The original frequency-weighted circle-arc phase. -/
@[expose] noncomputable def circlePhase (R h u : ℝ) : ℝ := h * Real.sqrt (2 * R * u - u ^ 2)

/-- The critical point of the original phase for a dual frequency. -/
@[expose] noncomputable def circleCriticalPoint (R h ν : ℝ) : ℝ :=
  R * (1 - ν / Real.sqrt (h ^ 2 + ν ^ 2))

/-- Positive dual frequencies give a critical point in the left semicircle. -/
theorem circleCriticalPoint_mem {R h ν : ℝ} (hR : 0 < R) (hh : 0 < h) (hν : 0 < ν) :
    circleCriticalPoint R h ν ∈ Set.Ioo 0 R := by
  have hD : 0 < h ^ 2 + ν ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg ν)
  have hs := Real.sq_sqrt hD.le
  have hs0 := Real.sqrt_nonneg (h ^ 2 + ν ^ 2)
  have hsν : ν < Real.sqrt (h ^ 2 + ν ^ 2) := by nlinarith only [hs, hs0, hν.le, sq_pos_of_pos hh]
  have hp : 0 < ν / Real.sqrt (h ^ 2 + ν ^ 2) := div_pos hν (hν.trans hsν)
  have hlt : ν / Real.sqrt (h ^ 2 + ν ^ 2) < 1 := (div_lt_one (hν.trans hsν)).mpr hsν
  unfold circleCriticalPoint
  constructor
  · exact mul_pos hR (sub_pos.mpr hlt)
  · nlinarith only [hR, hp]

/-- The circle height at the critical point, with the positive root fixed. -/
theorem sqrt_circleCriticalPoint {R h ν : ℝ} (hR : 0 < R) (hh : 0 < h) :
    Real.sqrt (2 * R * circleCriticalPoint R h ν - (circleCriticalPoint R h ν) ^ 2) =
      R * h / Real.sqrt (h ^ 2 + ν ^ 2) := by
  have hD : 0 < h ^ 2 + ν ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg ν)
  have hs0 : 0 < Real.sqrt (h ^ 2 + ν ^ 2) := Real.sqrt_pos.mpr hD
  have hs := Real.sq_sqrt hD.le
  have heq : 2 * R * circleCriticalPoint R h ν - (circleCriticalPoint R h ν) ^ 2 =
      (R * h / Real.sqrt (h ^ 2 + ν ^ 2)) ^ 2 := by
    unfold circleCriticalPoint
    field_simp
    nlinarith only [hs]
  rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos (mul_pos hR hh) hs0)]

/-- The derivative of the original circle phase on its left semicircle. -/
theorem hasDerivAt_circlePhase {R h u : ℝ} (hR : 0 < R) (hu : u ∈ Set.Ioo 0 R) :
    HasDerivAt (circlePhase R h) (h * (R - u) / Real.sqrt (2 * R * u - u ^ 2)) u := by
  have hD : 0 < 2 * R * u - u ^ 2 := by nlinarith only [hR, hu.1, hu.2]
  have hp := (((hasDerivAt_id u).const_mul (2 * R)).sub ((hasDerivAt_id u).pow 2)).sqrt hD.ne'
  have hh := hp.const_mul h
  convert hh using 1
  · funext x
    rfl
  · norm_num only [id_eq, Pi.sub_apply, Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one]
    field_simp

/-- The explicit point solves the actual stationary equation. -/
theorem hasDerivAt_circlePhase_critical {R h ν : ℝ} (hR : 0 < R) (hh : 0 < h) (hν : 0 < ν) :
    HasDerivAt (circlePhase R h) ν (circleCriticalPoint R h ν) := by
  have hp := hasDerivAt_circlePhase (h := h) hR (circleCriticalPoint_mem hR hh hν)
  convert hp using 1
  rw [sqrt_circleCriticalPoint hR hh]
  unfold circleCriticalPoint
  have hs0 : Real.sqrt (h ^ 2 + ν ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- Exact Legendre value, with no asymptotic approximation or amplitude hypothesis. -/
theorem circlePhase_sub_frequency_eq_dual {R h ν : ℝ} (hR : 0 < R) (hh : 0 < h) :
    circlePhase R h (circleCriticalPoint R h ν) - ν * circleCriticalPoint R h ν =
      circleDualPhase R h ν := by
  have hD : 0 < h ^ 2 + ν ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hh) (sq_nonneg ν)
  have hs := Real.sq_sqrt hD.le
  unfold circlePhase circleDualPhase
  rw [sqrt_circleCriticalPoint hR hh, ← Real.sqrt_eq_rpow]
  unfold circleCriticalPoint
  field_simp
  nlinarith only [hs]

end WaveTurbulence.VdCB
