/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleArc
import Mathlib.Tactic

/-!
# Geometric width bounds for circular height blocks

NT-CIRCLE-v2 goal 2: a left or right boundary interval on which the circle
height is at most `2H` has width at most `4H²/R`, uniformly in the center.
This supplies the interval-length input in the local sawtooth estimate.
-/

public section

namespace WaveTurbulence.Counting

/-- Circle height is monotone on the left semicircle. -/
theorem circleHeight_monotone_left {R c : ℝ} :
    MonotoneOn (circleHeight R c) (Set.Iic c) := by
  intro x hx y hy hxy
  apply Real.sqrt_le_sqrt
  have h1 : 0 ≤ c - y := sub_nonneg.mpr hy
  have h2 : c - y ≤ c - x := sub_le_sub_left hxy c
  have hsq := pow_le_pow_left₀ h1 h2 2
  nlinarith only [hsq]

/-- Width bound for a left boundary interval. A lower height cutoff is not
needed for this purely geometric estimate. -/
theorem circle_left_width_le {R c x y H : ℝ} (hR : 0 < R)
    (hxc : c - R ≤ x) (hxy : x ≤ y) (hyc : y ≤ c)
    (hh : circleHeight R c y ≤ 2 * H) :
    y - x ≤ 4 * H ^ 2 / R := by
  have habs : |y - c| ≤ R := abs_le.mpr ⟨by linarith only [hxc, hxy],
    by linarith only [hyc, hR]⟩
  have hysq := (sq_le_sq₀ (abs_nonneg (y - c)) hR.le).mpr habs
  simp only [sq_abs] at hysq
  have heq := circleHeight_sq hysq
  have hh2 := pow_le_pow_left₀ (show 0 ≤ circleHeight R c y from Real.sqrt_nonneg _) hh 2
  have hp : 0 ≤ (c - y) * (R - (c - y)) :=
    mul_nonneg (sub_nonneg.mpr hyc) (by linarith only [hxc, hxy])
  have hwidth : R * (y - x) ≤ R * (R - (c - y)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hxc]) hR.le
  rw [le_div_iff₀ hR]
  nlinarith only [heq, hh2, hp, hwidth]

end WaveTurbulence.Counting
