/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleArc
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Endpoint geometry for circular area quadrature

The slopes one unit away from the two tips are bounded by the square root
of the radius. These estimates control the Euler–Maclaurin remainder in
NT-CIRCLE-v2 goal 2.
-/

public section

namespace WaveTurbulence.Counting

/-- A circular height at distance at least one from either tip is at least
`sqrt R`. -/
theorem sqrt_radius_le_circleHeight {R c x : ℝ} (hR : 1 ≤ R)
    (hl : c-R+1 ≤ x) (hr : x ≤ c+R-1) :
    Real.sqrt R ≤ circleHeight R c x := by
  apply Real.sqrt_le_sqrt
  have ha : |x-c| ≤ R-1 := abs_le.mpr ⟨by linarith only [hl], by linarith only [hr]⟩
  have hs := sq_le_sq₀ (abs_nonneg (x-c)) (by linarith only [hR] : 0 ≤ R-1) |>.mpr ha
  rw [sq_abs] at hs
  nlinarith only [hs, hR]

/-- The absolute circular slope on the interval with unit tip regions removed
is bounded by `sqrt R`. -/
theorem abs_circleHeight_slope_le_sqrt {R c x : ℝ} (hR : 1 ≤ R)
    (hl : c-R+1 ≤ x) (hr : x ≤ c+R-1) :
    |-(x-c) / circleHeight R c x| ≤ Real.sqrt R := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hs := sqrt_radius_le_circleHeight hR hl hr
  have hp : 0 < circleHeight R c x := (Real.sqrt_pos.mpr hRp).trans_le hs
  rw [abs_div, abs_neg, abs_of_pos hp, div_le_iff₀ hp]
  have ha : |x-c| ≤ R := abs_le.mpr ⟨by linarith only [hl], by linarith only [hr]⟩
  calc
    _ ≤ R := ha
    _ = Real.sqrt R * Real.sqrt R := (Real.mul_self_sqrt hRp.le).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg R)

/-- Within two units of the left tip, the height is at most `2 * sqrt R`. -/
theorem circleHeight_le_two_sqrt_of_left_tip {R c x : ℝ} (hR : 0 ≤ R)
    (hr : x ≤ c-R+2) :
    circleHeight R c x ≤ 2 * Real.sqrt R := by
  have hb : R^2-(x-c)^2 ≤ (2 * Real.sqrt R)^2 := by
    have hs := Real.sq_sqrt hR
    have hm := mul_nonneg hR (by linarith only [hr] : 0 ≤ 2-(x-c+R))
    nlinarith only [sq_nonneg (x-c+R), hm, hs]
  change Real.sqrt (R^2-(x-c)^2) ≤ _
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · exact hb

/-- The reflected estimate within two units of the right tip. -/
theorem circleHeight_le_two_sqrt_of_right_tip {R c x : ℝ} (hR : 0 ≤ R)
    (hl : c+R-2 ≤ x) :
    circleHeight R c x ≤ 2 * Real.sqrt R := by
  have hb : R^2-(x-c)^2 ≤ (2 * Real.sqrt R)^2 := by
    have hs := Real.sq_sqrt hR
    have hm := mul_nonneg hR (by linarith only [hl] : 0 ≤ 2-(c+R-x))
    nlinarith only [sq_nonneg (c+R-x), hm, hs]
  change Real.sqrt (R^2-(x-c)^2) ≤ _
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · exact hb

open MeasureTheory intervalIntegral

/-- Exact area under a circular upper semicircle. -/
theorem integral_circleHeight {R c : ℝ} (hR : 0 < R) :
    (∫ x in c-R..c+R, circleHeight R c x) = Real.pi * R^2 / 2 := by
  have hscale (x : ℝ) : circleHeight R c x = R * Real.sqrt (1-((x-c)/R)^2) := by
    calc
      _ = Real.sqrt (R^2 * (1-((x-c)/R)^2)) := by
        unfold circleHeight
        congr 1
        field_simp
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR.le]
  simp_rw [hscale]
  rw [intervalIntegral.integral_const_mul]
  have ht := integral_comp_sub_right (fun x : ℝ => Real.sqrt (1-(x/R)^2)) c
    (a := c-R) (b := c+R)
  rw [ht]
  have ha : c-R-c = -R := by ring
  have hb : c+R-c = R := by ring
  rw [ha,hb, integral_comp_div (fun x : ℝ => Real.sqrt (1-x^2)) hR.ne']
  simp only [neg_div_self hR.ne', div_self hR.ne', smul_eq_mul, integral_sqrt_one_sub_sq]
  ring

end WaveTurbulence.Counting
