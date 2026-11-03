/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleHeightSum
public import WaveTurbulence.Foundations.Counting.CircleIntegerSawtooth
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Uniform circle discrepancy

NT-CIRCLE-v2 goal 2. The exact closed lattice disc uses the canonical frozen
unit-scale lattice embedding. All estimates are uniform in both real center
coordinates; boundary lattice points are included.
-/

public section

namespace WaveTurbulence.Counting

/-- The uniform two-thirds circle discrepancy bound, parametrized by the cube
root of the radius. -/
theorem abs_card_latticeDisc_cube_sub_area_le {r : ℝ} (hr : 1 ≤ r)
    (c : EuclideanSpace ℝ (Fin 2)) :
    |((latticeDisc c (r^3)).card:ℝ) - Real.pi*(r^3)^2| ≤ 1334*r^2 := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hr3 : 1 ≤ r^3 := by simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hr 3
  have hsqrt : Real.sqrt (r^3) ≤ r^2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact sq_nonneg r
    · have hm := mul_nonneg (pow_nonneg hr0 3) (sub_nonneg.mpr hr)
      nlinarith only [hm]
  have hh := abs_le.mp (abs_integer_circleHeight_sum_sub_area_le_one (c := c 0) hr3)
  have hp := abs_le.mp (circle_integer_sawtooth_sum_le (c := c 0) (d := c 1) hr)
  have hm := abs_le.mp (circle_integer_sawtooth_sum_le (c := c 0) (d := -(c 1)) hr)
  simp only [← sub_eq_add_neg] at hm
  rw [card_latticeDisc_eq_height_sub_sawtooth]
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, add_comm (c 1)]
  apply abs_le.mpr
  constructor <;> linarith only [hh.1,hh.2,hp.1,hp.2,hm.1,hm.2,hsqrt]

/-- NT-CIRCLE-v2 goal 2: the two-thirds circle-problem bound, uniformly in
all real centers, for the actual closed lattice disc and every radius `Q ≥ 1`. -/
theorem abs_card_latticeDisc_sub_area_le {Q : ℝ} (hQ : 1 ≤ Q)
    (c : EuclideanSpace ℝ (Fin 2)) :
    |((latticeDisc c Q).card:ℝ) - Real.pi*Q^2| ≤ 1334 * Q^((2:ℝ)/3) := by
  let r : ℝ := Q^((1:ℝ)/3)
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hr : 1 ≤ r := Real.one_le_rpow hQ (by norm_num)
  have hc : r^3 = Q := by
    simpa only [r, one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hQ0 (show (3:ℕ) ≠ 0 by decide)
  have hs : r^2 = Q^((2:ℝ)/3) := by
    change (Q^((1:ℝ)/3))^2 = _
    rw [← Real.rpow_mul_natCast hQ0]
    congr 1
    norm_num
  simpa only [hc,hs] using abs_card_latticeDisc_cube_sub_area_le hr c

end WaveTurbulence.Counting
