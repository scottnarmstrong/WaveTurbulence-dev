/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.StationaryErrorBounds
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The total endpoint-guard cost at the actual balanced circle radius

The guard intervals have radius upper-curvature times the chosen spatial
radius. Their integer count times the uniform curvature integral bound is
at most an absolute multiple of the same improved local circle powers.
-/

public section

namespace WaveTurbulence.NumberTheory

private theorem curvature_rpow {w U : ℝ} (hw : 0 < w) (hU : 0 < U) (s : ℝ) :
    (w*U^(-((3:ℝ)/2))/8)^s = (8:ℝ)^(-s)*w^s*U^((-((3:ℝ)/2))*s) := by
  rw [Real.div_rpow (by positivity : 0 ≤ w*U^(-((3:ℝ)/2))) (by norm_num),
    Real.mul_rpow hw.le (Real.rpow_nonneg hU.le _),← Real.rpow_mul hU.le,
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 8)]
  ring

/-- The spatial radius times square-root curvature has the small guard scale. -/
theorem circle_radius_mul_sqrt_curvature_le {w U : ℝ} (hw : 1 ≤ w) (hU : 1 ≤ U) :
    stationaryBalancingRadius w U*Real.sqrt (w*U^(-((3:ℝ)/2))/8) ≤
      w^((1:ℝ)/10)*U^((1:ℝ)/20) := by
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have hUp : 0 < U := zero_lt_one.trans_le hU
  rw [Real.sqrt_eq_rpow,curvature_rpow hwp hUp]
  have he : stationaryBalancingRadius w U*((8:ℝ)^(-((1:ℝ)/2))*w^((1:ℝ)/2)*
      U^((-((3:ℝ)/2))*((1:ℝ)/2))) =
      ((8:ℝ)^(-((1:ℝ)/2))/4)*(w^((1:ℝ)/10)*U^((1:ℝ)/20)) := by
    unfold stationaryBalancingRadius
    calc
      _ = ((8:ℝ)^(-((1:ℝ)/2))/4)*
          ((w^(-((2:ℝ)/5))*w^((1:ℝ)/2))*(U^((4:ℝ)/5)*U^(-((3:ℝ)/4)))) := by norm_num; ring
      _ = _ := by rw [← Real.rpow_add hwp,← Real.rpow_add hUp]; norm_num
  rw [he]
  have hcoef : (8:ℝ)^(-((1:ℝ)/2))/4 ≤ 1 := by
    have hh := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1:ℝ) ≤ 8)
      (by norm_num : -((1:ℝ)/2) ≤ 0)
    linarith only [hh]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef
    (by positivity : 0 ≤ w^((1:ℝ)/10)*U^((1:ℝ)/20))

/-- Reciprocal square-root curvature has the other guard scale. -/
theorem circle_inv_sqrt_curvature_le {w U : ℝ} (hw : 1 ≤ w) (hU : 1 ≤ U) :
    1/Real.sqrt (w*U^(-((3:ℝ)/2))/8) ≤ 3*(w^(-((1:ℝ)/2))*U^((3:ℝ)/4)) := by
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have hUp : 0 < U := zero_lt_one.trans_le hU
  rw [Real.sqrt_eq_rpow,one_div,← Real.rpow_neg (by positivity : 0 ≤ w*U^(-((3:ℝ)/2))/8),
    curvature_rpow hwp hUp]
  norm_num only [neg_neg,show (-((3:ℝ)/2))*(-((1:ℝ)/2)) = 3/4 by norm_num]
  have hc : (8:ℝ)^((1:ℝ)/2) ≤ 3 := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hwp.le (-((1:ℝ)/2))))
    (Real.rpow_nonneg hUp.le ((3:ℝ)/4))

/-- Count times uniform curvature bound for both endpoint guard intervals
at their actual balanced radius. -/
theorem circle_total_guard_error_le {w U G : ℝ}
    (hw : 1 ≤ w) (hU : 1 ≤ U) (hUw : U ≤ w^2) (hwU : w ≤ U^2)
    (hG : G ≤ 4*(w*U^(-((3:ℝ)/2)))*stationaryBalancingRadius w U+2) :
    G*(4/Real.sqrt (w*U^(-((3:ℝ)/2))/8)) ≤
      512*(w^((11:ℝ)/30)*U^((7:ℝ)/20)) := by
  let mu : ℝ := w*U^(-((3:ℝ)/2))/8
  have hmu : 0 < mu := by dsimp only [mu]; positivity
  have hs : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu
  have hquot : mu/Real.sqrt mu = Real.sqrt mu := by
    apply (div_eq_iff hs.ne').mpr
    exact (Real.mul_self_sqrt hmu.le).symm
  have hrad := circle_radius_mul_sqrt_curvature_le hw hU
  have hinv := circle_inv_sqrt_curvature_le hw hU
  have hscale := stationary_error_scales_le_local_circle_scale hw hU hUw hwU
  have hpos1 : 0 ≤ w^((2:ℝ)/5)*U^((1:ℝ)/5) := by positivity
  change G*(4/Real.sqrt mu) ≤ _
  calc
    _ ≤ (4*(w*U^(-((3:ℝ)/2)))*stationaryBalancingRadius w U+2)*(4/Real.sqrt mu) :=
      mul_le_mul_of_nonneg_right hG (by positivity)
    _ = 128*(stationaryBalancingRadius w U*Real.sqrt mu)+8*(1/Real.sqrt mu) := by
      calc
        _ = 128*stationaryBalancingRadius w U*(mu/Real.sqrt mu)+8*(1/Real.sqrt mu) := by
          dsimp only [mu]; ring
        _ = _ := by rw [hquot]; ring
    _ ≤ 128*(w^((1:ℝ)/10)*U^((1:ℝ)/20))+24*(w^(-((1:ℝ)/2))*U^((3:ℝ)/4)) := by
      linarith only [hrad,hinv]
    _ ≤ _ := by
      have hpos2 : 0 ≤ w^(-((1:ℝ)/2))*U^((3:ℝ)/4) := by positivity
      linarith only [hscale,hpos1,hpos2]

end WaveTurbulence.NumberTheory
