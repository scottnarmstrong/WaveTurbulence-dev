/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleQuadrature
public import WaveTurbulence.Foundations.Counting.IntegerSampling
import Mathlib.Tactic

/-!
# Circular height sums over the actual integer columns

Uniform area comparison for the vertical slicing formula in NT-CIRCLE-v2.
-/

public section

namespace WaveTurbulence.Counting

/-- Uniform square-root error for the integer height sum, for radius at least two. -/
theorem abs_integer_circleHeight_sum_sub_area_le {R c : ℝ} (hR : 2 ≤ R) :
    |(∑ x ∈ integerInterval (c-R) (c+R), circleHeight R c x) - Real.pi*R^2/2| ≤
      15 * Real.sqrt R := by
  let L : ℤ := ⌈c-R⌉
  let U : ℤ := ⌊c+R⌋
  have hL : c-R ≤ (L:ℝ) := Int.le_ceil _
  have hL' : (L:ℝ) < c-R+1 := Int.ceil_lt_add_one _
  have hU : (U:ℝ) ≤ c+R := Int.floor_le _
  have hU' : c+R-1 < (U:ℝ) := Int.sub_one_lt_floor _
  have hlenR : (2:ℝ) ≤ (U:ℝ)-(L:ℝ) := by linarith only [hL',hU',hR]
  have hlen : (2:ℤ) ≤ U-L := by exact_mod_cast hlenR
  let N : ℕ := (U-L-2).toNat
  have hz : (N:ℤ) = U-L-2 := Int.toNat_of_nonneg (by omega)
  have hzR : (N:ℝ) = (U:ℝ)-(L:ℝ)-2 := by exact_mod_cast hz
  have he : (L:ℝ)+N+2 = U := by linarith only [hzR]
  have hM : (U+1-L).toNat = N+3 := by omega
  change |(∑ x ∈ Finset.Icc L U, circleHeight R c x) - _| ≤ _
  rw [sum_int_Icc_eq_range, hM]
  apply abs_circle_sample_sum_sub_area_le N (by linarith only [hR]) hL hL'.le
  · rw [he]; exact hU
  · rw [he]; exact hU'.le

/-- Uniform area comparison for all radii at least one. -/
theorem abs_integer_circleHeight_sum_sub_area_le_one {R c : ℝ} (hR : 1 ≤ R) :
    |(∑ x ∈ integerInterval (c-R) (c+R), circleHeight R c x) - Real.pi*R^2/2| ≤
      15 * Real.sqrt R := by
  by_cases hlarge : 2 ≤ R
  · exact abs_integer_circleHeight_sum_sub_area_le hlarge
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hR2 : R ≤ 2 := (not_le.mp hlarge).le
  have hcard := card_integerInterval_eq_sawtooth (l := c-R) (u := c+R)
    (by linarith only [hR])
  have hs1 := NumberTheory.abs_sawtooth_le_half (c+R)
  have hs2 := NumberTheory.abs_sawtooth_le_half (-(c-R))
  have hc : ((integerInterval (c-R) (c+R)).card:ℝ) ≤ 5 := by
    have h1 := neg_abs_le (NumberTheory.sawtooth (c+R))
    have h2 := neg_abs_le (NumberTheory.sawtooth (-(c-R)))
    linarith only [hcard,hs1,hs2,h1,h2,hR2]
  have hh (x : ℝ) : circleHeight R c x ≤ 2 := by
    apply le_trans ?_ hR2
    change Real.sqrt (R^2-(x-c)^2) ≤ R
    exact Real.sqrt_le_iff.mpr ⟨hR0, sub_le_self _ (sq_nonneg _)⟩
  have hsum0 : 0 ≤ ∑ x ∈ integerInterval (c-R) (c+R), circleHeight R c x :=
    Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hsum : (∑ x ∈ integerInterval (c-R) (c+R), circleHeight R c x) ≤ 10 := by
    calc
      _ ≤ ∑ _x ∈ integerInterval (c-R) (c+R), (2:ℝ) :=
        Finset.sum_le_sum (fun x _ => hh x)
      _ = 2 * ((integerInterval (c-R) (c+R)).card:ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 10 := by linarith only [hc]
  have harea0 : 0 ≤ Real.pi*R^2/2 := by positivity
  have harea : Real.pi*R^2/2 ≤ 8 := by
    have hs : R^2 ≤ 4 := by nlinarith only [hR0,hR2]
    have hm := mul_le_mul Real.pi_lt_four.le hs (sq_nonneg R) (by norm_num : (0:ℝ) ≤ 4)
    linarith only [hm]
  have hsqrt : 1 ≤ Real.sqrt R := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hR
  apply abs_le.mpr
  constructor <;> linarith only [hsum0,hsum,harea0,harea,hsqrt]

end WaveTurbulence.Counting
