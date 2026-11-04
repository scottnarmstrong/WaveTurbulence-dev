/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.StationaryRadius
public import WaveTurbulence.Foundations.NumberTheory.PowerScaleComparison
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Quantitative stationary error scales for the circle application

The actual balancing radius controls the explicit cubic and tail errors.
Their frequency-summed scale and the near-endpoint curvature terms fit the
local `(11/30,16/30)` circle powers. These are scalar comparisons, not an
assumed B-process formula or transformed exponential-sum estimate.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- The explicit sharp stationary errors are at most an absolute constant
times their common balanced scale, for any actual curvature above the lower
source curvature. -/
theorem stationary_radius_error_le {w U q : ℝ} (hw : 0 < w) (hU : 0 < U)
    (hq : w*U^(-((3:ℝ)/2))/8 ≤ q) :
    (2*Real.pi/3)*(3*w*U^(-((5:ℝ)/2)))*(stationaryBalancingRadius w U)^4+
      2/(Real.pi*(q*stationaryBalancingRadius w U))+
      2/(Real.pi*((w*U^(-((3:ℝ)/2))/8)*stationaryBalancingRadius w U)) ≤
        256*(w^(-((3:ℝ)/5))*U^((7:ℝ)/10)) := by
  let r := stationaryBalancingRadius w U
  let mu : ℝ := w*U^(-((3:ℝ)/2))/8
  let E : ℝ := w^(-((3:ℝ)/5))*U^((7:ℝ)/10)
  have hr : 0 < r := stationaryBalancingRadius_pos hw hU
  have hmu : 0 < mu := by dsimp only [mu]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have htail : 2/(Real.pi*(q*r)) ≤ 2/(Real.pi*(mu*r)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq hr.le) Real.pi_pos.le)
  have hcubic : (2*Real.pi/3)*(3*w*U^(-((5:ℝ)/2)))*r^4 = (2*Real.pi/256)*E := by
    calc
      _ = 2*Real.pi*((w*U^(-((5:ℝ)/2)))*r^4) := by ring
      _ = _ := by rw [stationary_radius_cubic_term hw hU]; dsimp only [E]; ring
  have htailEq : 4/(Real.pi*(mu*r)) = (128/Real.pi)*E := by
    rw [div_mul_eq_div_div]
    calc
      _ = (4/Real.pi)*(1/(mu*r)) := by ring
      _ = _ := by rw [stationary_radius_tail_term hw hU]; dsimp only [E]; ring
  have hpi : 1 ≤ Real.pi := by linarith only [Real.pi_gt_three]
  have hdiv : 128/Real.pi ≤ 128 := div_le_self (by norm_num) hpi
  have hcoef : 2*Real.pi/256+128/Real.pi ≤ 256 := by
    nlinarith only [hdiv,Real.pi_lt_four]
  change (2*Real.pi/3)*(3*w*U^(-((5:ℝ)/2)))*r^4+
    2/(Real.pi*(q*r))+2/(Real.pi*(mu*r)) ≤ 256*E
  calc
    _ ≤ (2*Real.pi/3)*(3*w*U^(-((5:ℝ)/2)))*r^4+4/(Real.pi*(mu*r)) := by
      calc
        _ ≤ (2*Real.pi/3)*(3*w*U^(-((5:ℝ)/2)))*r^4+
            (2/(Real.pi*(mu*r))+2/(Real.pi*(mu*r))) := by linarith only [htail]
        _ = _ := by ring
    _ = (2*Real.pi/256+128/Real.pi)*E := by rw [hcubic,htailEq]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE

/-- Large frequency relative to a short source block is covered directly
by the actual trivial sample count. -/
theorem local_circle_scale_dominates_length {w U : ℝ} (hU : 1 ≤ U) (hw : 0 < w)
    (hlarge : U^2 ≤ w) : U ≤ w^((11:ℝ)/30)*U^((7:ℝ)/20) := by
  have he := rpow_mul_le_of_lower_scale hU hw (l := 2) (a := 0) (b := 1)
    (c := (11:ℝ)/30) (d := (7:ℝ)/20) (by simpa only [Real.rpow_two] using hlarge)
    (by norm_num) (by norm_num)
  simpa only [Real.rpow_zero,Real.rpow_one,one_mul] using he

/-- In the complementary frequency range, all balanced stationary and
near-endpoint error scales fit the same local circle powers. -/
theorem stationary_error_scales_le_local_circle_scale {w U : ℝ}
    (hw : 1 ≤ w) (hU : 1 ≤ U) (hUw : U ≤ w^2) (hwU : w ≤ U^2) :
    w^((2:ℝ)/5)*U^((1:ℝ)/5)+w^((1:ℝ)/10)*U^((1:ℝ)/20)+
      w^(-((1:ℝ)/2))*U^((3:ℝ)/4)+1 ≤ 4*(w^((11:ℝ)/30)*U^((7:ℝ)/20)) := by
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have h1 := rpow_mul_le_of_upper_scale hU hwp (u := 2)
    (a := (2:ℝ)/5) (b := (1:ℝ)/5) (c := (11:ℝ)/30) (d := (7:ℝ)/20)
    (by simpa only [Real.rpow_two] using hwU) (by norm_num) (by norm_num)
  have h2 := rpow_mul_le_of_lower_scale hU hwp (l := 0)
    (a := (1:ℝ)/10) (b := (1:ℝ)/20) (c := (11:ℝ)/30) (d := (7:ℝ)/20)
    (by simpa only [Real.rpow_zero] using hw) (by norm_num) (by norm_num)
  have hsqrt : U^((1:ℝ)/2) ≤ w := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.mpr ⟨le_trans zero_le_one hw,hUw⟩
  have h3 := rpow_mul_le_of_lower_scale hU hwp hsqrt
    (a := -((1:ℝ)/2)) (b := (3:ℝ)/4) (c := (11:ℝ)/30) (d := (7:ℝ)/20)
    (by norm_num) (by norm_num)
  have hpw := Real.one_le_rpow hw (by norm_num : (0:ℝ) ≤ 11/30)
  have hpu := Real.one_le_rpow hU (by norm_num : (0:ℝ) ≤ 7/20)
  have h4 : 1 ≤ w^((11:ℝ)/30)*U^((7:ℝ)/20) := by
    nlinarith only [hpw,hpu,mul_nonneg (sub_nonneg.mpr hpw) (sub_nonneg.mpr hpu)]
  linarith only [h1,h2,h3,h4]

end WaveTurbulence.NumberTheory
