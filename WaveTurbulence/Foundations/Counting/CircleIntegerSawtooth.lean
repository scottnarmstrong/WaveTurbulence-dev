/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.IntegerSampling
public import WaveTurbulence.Foundations.Counting.CircleSemicircle
import Mathlib.Tactic

/-!
# Uniform sawtooth cancellation over integer circle columns

The translated natural-interval estimate is reindexed to the actual closed
integer column interval used in lattice-disc counting. NT-CIRCLE-v2 goal 2.
-/

public section

namespace WaveTurbulence.Counting

/-- Uniform cancellation for all columns of a circle of radius `r³`. -/
theorem circle_integer_sawtooth_sum_le {r c d : ℝ} (hr : 1 ≤ r) :
    |∑ x ∈ integerInterval (c-r^3) (c+r^3),
      NumberTheory.sawtooth (circleHeight (r^3) c x+d)| ≤ 652*r^2 := by
  let L : ℤ := ⌈c-r^3⌉
  let U : ℤ := ⌊c+r^3⌋
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hLU : L ≤ U+1 := (Int.ceil_mono (by linarith only [pow_nonneg hr0 3] : c-r^3 ≤ c+r^3)).trans
    (Int.ceil_le_floor_add_one _)
  have hM : (((U+1-L).toNat : ℕ):ℤ) = U+1-L := Int.toNat_of_nonneg (by omega)
  have hMR : ((U+1-L).toNat:ℝ) = (U:ℝ)+1-(L:ℝ) := by exact_mod_cast hM
  change |∑ x ∈ Finset.Icc L U,
    NumberTheory.sawtooth (circleHeight (r^3) c x+d)| ≤ _
  rw [sum_int_Icc_eq_range (fun x : ℝ => NumberTheory.sawtooth (circleHeight (r^3) c x+d)),
    sum_range_eq_Ioc (fun x : ℝ => NumberTheory.sawtooth (circleHeight (r^3) c x+d))]
  apply circle_sawtooth_sum_le hr
  · have hL : c-r^3 ≤ (L:ℝ) := Int.le_ceil _
    norm_num only [Nat.cast_zero]
    linarith only [hL]
  · have hU : (U:ℝ) ≤ c+r^3 := Int.floor_le _
    linarith only [hMR,hU]

end WaveTurbulence.Counting
