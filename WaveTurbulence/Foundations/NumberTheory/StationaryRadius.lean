/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A radius balancing the circle stationary-phase errors

For curvature scale `w*U^(-3/2)` and cubic scale `w*U^(-5/2)`, this actual
positive radius balances the cubic remainder and nonstationary tails.
All statements here are scalar; no stationary-phase estimate is assumed.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- A quarter of the balanced local stationary radius. -/
@[expose] noncomputable def stationaryBalancingRadius (w U : ℝ) : ℝ :=
  U^((4:ℝ)/5)*w^(-((2:ℝ)/5))/4

theorem stationaryBalancingRadius_pos {w U : ℝ} (hw : 0 < w) (hU : 0 < U) :
    0 < stationaryBalancingRadius w U := by unfold stationaryBalancingRadius; positivity

/-- The chosen radius always fits in a quarter of the source block. -/
theorem stationaryBalancingRadius_le_quarter {w U : ℝ} (hw : 1 ≤ w) (hU : 1 ≤ U) :
    stationaryBalancingRadius w U ≤ U/4 := by
  unfold stationaryBalancingRadius
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hu := Real.rpow_le_self_of_one_le hU (by norm_num : (4:ℝ)/5 ≤ 1)
  have hw' := Real.rpow_le_one_of_one_le_of_nonpos hw (by norm_num : -((2:ℝ)/5) ≤ 0)
  simpa only [mul_one] using mul_le_mul hu hw'
    (Real.rpow_nonneg (le_trans zero_le_one hw) _) (le_trans zero_le_one hU)

/-- Exact cubic error at the chosen radius. -/
theorem stationary_radius_cubic_term {w U : ℝ} (hw : 0 < w) (hU : 0 < U) :
    (w*U^(-((5:ℝ)/2)))*(stationaryBalancingRadius w U)^4 =
      (w^(-((3:ℝ)/5))*U^((7:ℝ)/10))/256 := by
  have hu4 : (U^((4:ℝ)/5))^4 = U^((16:ℝ)/5) := by
    rw [← Real.rpow_mul_natCast hU.le ((4:ℝ)/5) 4]
    congr 1
    norm_num
  have hw4 : (w^(-((2:ℝ)/5)))^4 = w^(-((8:ℝ)/5)) := by
    rw [← Real.rpow_mul_natCast hw.le (-((2:ℝ)/5)) 4]
    congr 1
    norm_num
  have hwid : w*w^(-((8:ℝ)/5)) = w^(-((3:ℝ)/5)) := by
    have he := Real.rpow_add hw (1:ℝ) (-((8:ℝ)/5))
    norm_num only [Real.rpow_one,show (1:ℝ)+(-(8/5)) = -(3/5) by norm_num] at he
    exact he.symm
  have huid : U^(-((5:ℝ)/2))*U^((16:ℝ)/5) = U^((7:ℝ)/10) := by
    have he := Real.rpow_add hU (-((5:ℝ)/2)) ((16:ℝ)/5)
    norm_num only [show (-((5:ℝ)/2))+(16/5) = 7/10 by norm_num] at he
    exact he.symm
  unfold stationaryBalancingRadius
  rw [div_pow,mul_pow,hu4,hw4,show (4:ℝ)^4 = 256 by norm_num]
  calc
    _ = (w*w^(-((8:ℝ)/5)))*(U^(-((5:ℝ)/2))*U^((16:ℝ)/5))/256 := by ring
    _ = _ := by rw [hwid,huid]

/-- Exact reciprocal-curvature error at the same actual radius. -/
theorem stationary_radius_tail_term {w U : ℝ} (hw : 0 < w) (hU : 0 < U) :
    1/((w*U^(-((3:ℝ)/2))/8)*stationaryBalancingRadius w U) =
      32*(w^(-((3:ℝ)/5))*U^((7:ℝ)/10)) := by
  have hwid : w*w^(-((2:ℝ)/5))*w^(-((3:ℝ)/5)) = 1 := by
    calc
      _ = w^(((1:ℝ)+(-(2/5)))+(-(3/5))) := by
        rw [Real.rpow_add hw,Real.rpow_add hw,Real.rpow_one]
      _ = _ := by norm_num
  have huid : U^(-((3:ℝ)/2))*U^((4:ℝ)/5)*U^((7:ℝ)/10) = 1 := by
    calc
      _ = U^(((-((3:ℝ)/2))+(4/5))+(7/10)) := by rw [Real.rpow_add hU,Real.rpow_add hU]
      _ = _ := by norm_num
  have hprod : ((w*U^(-((3:ℝ)/2))/8)*stationaryBalancingRadius w U)*
      (w^(-((3:ℝ)/5))*U^((7:ℝ)/10)) = 1/32 := by
    unfold stationaryBalancingRadius
    calc
      _ = (w*w^(-((2:ℝ)/5))*w^(-((3:ℝ)/5)))*
          (U^(-((3:ℝ)/2))*U^((4:ℝ)/5)*U^((7:ℝ)/10))/32 := by ring
      _ = _ := by rw [hwid,huid]; norm_num
  have hd : 0 < (w*U^(-((3:ℝ)/2))/8)*stationaryBalancingRadius w U :=
    mul_pos (by positivity) (stationaryBalancingRadius_pos hw hU)
  apply (div_eq_iff hd.ne').mpr
  nlinarith only [hprod]

end WaveTurbulence.NumberTheory
