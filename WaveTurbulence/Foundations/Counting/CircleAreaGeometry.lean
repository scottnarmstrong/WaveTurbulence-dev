/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleArc
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

end WaveTurbulence.Counting
