/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleAreaGeometry
import Mathlib.Tactic

/-!
# Area identities at the circular octant cut

The central excess and the clipped semicircle have explicit areas. These
identities account exactly for the central square in the cap decomposition.
-/

public section

namespace WaveTurbulence.Counting

open MeasureTheory intervalIntegral Set

/-- Area of the normalized central circular arc. -/
theorem integral_sqrt_one_sub_sq_octant :
    (∫ x in (-(1/Real.sqrt 2):ℝ)..(1/Real.sqrt 2), Real.sqrt (1-x^2)) =
      Real.pi/4+1/2 := by
  have hs : (1:ℝ)/Real.sqrt 2 = Real.sqrt 2/2 := (Real.sqrt_div_self' (x := 2)).symm
  calc
    _ = ∫ x in Real.sin (-(Real.pi/4))..Real.sin (Real.pi/4), Real.sqrt (1-x^2) := by
      rw [Real.sin_neg,Real.sin_pi_div_four,hs]
    _ = ∫ x in (-(Real.pi/4))..(Real.pi/4), Real.sqrt (1-Real.sin x^2)*Real.cos x :=
      (integral_comp_mul_deriv (fun x _ => Real.hasDerivAt_sin x)
        Real.continuous_cos.continuousOn (by fun_prop)).symm
    _ = ∫ x in (-(Real.pi/4))..(Real.pi/4), Real.cos x^2 := by
      apply integral_congr_ae (ae_of_all _ (fun x hx => ?_))
      rw [uIoc_of_le (by linarith only [Real.pi_pos] : -(Real.pi/4) ≤ Real.pi/4)] at hx
      rw [← Real.cos_eq_sqrt_one_sub_sin_sq
        (by linarith only [hx.1,Real.pi_pos]) (by linarith only [hx.2,Real.pi_pos]),pow_two]
    _ = Real.pi/4+1/2 := by
      rw [integral_cos_sq]
      simp only [Real.cos_neg,Real.sin_neg,Real.cos_pi_div_four,Real.sin_pi_div_four]
      nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- Central arc area, uniformly in the translated horizontal center. -/
theorem integral_circleHeight_central {R c : ℝ} (hR : 0 < R) :
    (∫ x in c-R/Real.sqrt 2..c+R/Real.sqrt 2, circleHeight R c x) =
      R^2*(Real.pi/4+1/2) := by
  have hscale (x : ℝ) : circleHeight R c x = R*Real.sqrt (1-((x-c)/R)^2) := by
    calc
      _ = Real.sqrt (R^2*(1-((x-c)/R)^2)) := by
        unfold circleHeight
        congr 1
        field_simp
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg R),Real.sqrt_sq hR.le]
  simp_rw [hscale]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_comp_sub_right (fun x : ℝ => Real.sqrt (1-(x/R)^2)) c]
  have ha : c-R/Real.sqrt 2-c = -(R/Real.sqrt 2) := by ring
  have hb : c+R/Real.sqrt 2-c = R/Real.sqrt 2 := by ring
  rw [ha,hb,integral_comp_div (fun x : ℝ => Real.sqrt (1-x^2)) hR.ne']
  have he : (R/Real.sqrt 2)/R = 1/Real.sqrt 2 := by field_simp
  rw [neg_div,he,integral_sqrt_one_sub_sq_octant]
  simp only [smul_eq_mul]
  ring

/-- Exact area of the central excess over the inscribed square. -/
theorem integral_circle_central_excess {R c : ℝ} (hR : 0 < R) :
    (∫ x in c-R/Real.sqrt 2..c+R/Real.sqrt 2,
      (circleHeight R c x-R/Real.sqrt 2)) = R^2*(Real.pi/4-1/2) := by
  have hc : Continuous (circleHeight R c) := by unfold circleHeight; fun_prop
  rw [integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
    integral_circleHeight_central hR,intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  have hs : (R/Real.sqrt 2)^2 = R^2/2 := by
    rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith only [hs]

end WaveTurbulence.Counting
