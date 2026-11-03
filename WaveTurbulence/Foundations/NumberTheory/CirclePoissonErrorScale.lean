/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.StationaryErrorBounds
public import WaveTurbulence.Foundations.VdCB.TruncatedPoisson
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Absorbing the actual truncated Poisson error in the local circle powers

The logarithmic error is bounded by a fixed power before optimizing the
sawtooth cutoff. There is no logarithmic loss in the final local exponent.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The logarithm of a frequency width at most three times the source
frequency scale fits the local circle power, with an absolute constant. -/
theorem log_le_local_circle_scale {w U x : ℝ} (hw : 1 ≤ w) (hU : 1 ≤ U)
    (hx : 0 ≤ x) (hxw : x ≤ 3*w) :
    Real.log x ≤ 12*(w^((11:ℝ)/30)*U^((7:ℝ)/20)) := by
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have hp : x^((1:ℝ)/4) ≤ 3*w^((1:ℝ)/4) := by
    calc
      _ ≤ (3*w)^((1:ℝ)/4) := Real.rpow_le_rpow hx hxw (by norm_num)
      _ = (3:ℝ)^((1:ℝ)/4)*w^((1:ℝ)/4) := Real.mul_rpow (by norm_num) hwp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ) ≤ 3) (by norm_num : (1:ℝ)/4 ≤ 1))
        (Real.rpow_nonneg hwp.le _)
  have hpw : w^((1:ℝ)/4) ≤ w^((11:ℝ)/30) := Real.rpow_le_rpow_of_exponent_le hw (by norm_num)
  have hpu : 1 ≤ U^((7:ℝ)/20) := Real.one_le_rpow hU (by norm_num)
  have hlocal : w^((1:ℝ)/4) ≤ w^((11:ℝ)/30)*U^((7:ℝ)/20) :=
    hpw.trans (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hpu
      (Real.rpow_nonneg hwp.le ((11:ℝ)/30))))
  have hlog := Real.log_le_rpow_div hx (by norm_num : (0:ℝ) < 1/4)
  linarith only [hlog,hp,hlocal]

/-- A width bounded by four times the frequency scale has the same local power. -/
theorem log_le_local_circle_scale_four {w U x : ℝ} (hw : 1 ≤ w) (hU : 1 ≤ U)
    (hx : 0 ≤ x) (hxw : x ≤ 4*w) :
    Real.log x ≤ 16*(w^((11:ℝ)/30)*U^((7:ℝ)/20)) := by
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have hp : x^((1:ℝ)/4) ≤ 4*w^((1:ℝ)/4) := by
    calc
      _ ≤ (4*w)^((1:ℝ)/4) := Real.rpow_le_rpow hx hxw (by norm_num)
      _ = (4:ℝ)^((1:ℝ)/4)*w^((1:ℝ)/4) := Real.mul_rpow (by norm_num) hwp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ) ≤ 4) (by norm_num : (1:ℝ)/4 ≤ 1))
        (Real.rpow_nonneg hwp.le _)
  have hpw : w^((1:ℝ)/4) ≤ w^((11:ℝ)/30) := Real.rpow_le_rpow_of_exponent_le hw (by norm_num)
  have hpu : 1 ≤ U^((7:ℝ)/20) := Real.one_le_rpow hU (by norm_num)
  have hlocal : w^((1:ℝ)/4) ≤ w^((11:ℝ)/30)*U^((7:ℝ)/20) :=
    hpw.trans (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hpu
      (Real.rpow_nonneg hwp.le ((11:ℝ)/30))))
  have hlog := Real.log_le_rpow_div hx (by norm_num : (0:ℝ) < 1/4)
  linarith only [hlog,hp,hlocal]

/-- The precise error of the landed sharp truncated Poisson theorem fits
one fixed multiple of the local improved circle scale. -/
theorem truncated_poisson_error_le_local_circle_scale {w U : ℝ} (hw : 1 ≤ w)
    (hU : 1 ≤ U) (N : ℕ) (hN : (N:ℝ)+1 ≤ 3*w) :
    (2*(1+Real.log N)+4*Real.log ((N:ℝ)+1))/(2*Real.pi)+1 ≤
      80*(w^((11:ℝ)/30)*U^((7:ℝ)/20)) := by
  let L : ℝ := w^((11:ℝ)/30)*U^((7:ℝ)/20)
  have hL : 1 ≤ L := by
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hw (by norm_num))
      (Real.one_le_rpow hU (by norm_num))
  have hlog := log_le_local_circle_scale hw hU (Nat.cast_nonneg N)
    (show (N:ℝ) ≤ 3*w by linarith only [hN])
  have hlog' := log_le_local_circle_scale hw hU
    (show (0:ℝ) ≤ (N:ℝ)+1 by positivity) hN
  have hpos : 0 ≤ 2*(1+Real.log N)+4*Real.log ((N:ℝ)+1) := by
    have h1 := Real.log_natCast_nonneg N
    have h2 : 0 ≤ Real.log ((N:ℝ)+1) := Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) N])
    positivity
  have hden : 1 ≤ 2*Real.pi := by linarith only [Real.pi_gt_three]
  have hdiv := div_le_self hpos hden
  change (2*(1+Real.log N)+4*Real.log ((N:ℝ)+1))/(2*Real.pi)+1 ≤ 80*L
  linarith only [hdiv,hlog,hlog',hL]

end WaveTurbulence.NumberTheory
