/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleAreaGeometry
public import WaveTurbulence.Foundations.Counting.EulerMaclaurin
import Mathlib.Tactic

/-!
# Quadrature of circular heights

The middle interval has Euler–Maclaurin error of order `sqrt R`, uniformly
in the circle center. NT-CIRCLE-v2 goal 2.
-/

public section

namespace WaveTurbulence.Counting

open MeasureTheory intervalIntegral Set

/-- Circular quadrature away from the two unit tip regions. -/
theorem abs_circle_trapezoid_sub_integral_le {R c a : ℝ} (N : ℕ) (hR : 1 ≤ R)
    (hl : c-R+1 ≤ a) (hr : a+N ≤ c+R-1) :
    |(∑ k ∈ Finset.range (N+1), circleHeight R c (a+k)) -
      (circleHeight R c a + circleHeight R c (a+N))/2 -
      (∫ x in a..a+N, circleHeight R c x)| ≤ Real.sqrt R / 4 := by
  have hinside (x : ℝ) (hx : x ∈ Icc a (a+N)) : (x-c)^2 < R^2 := by
    have ha : |x-c| < R := abs_lt.mpr ⟨by linarith only [hl,hx.1], by linarith only [hr,hx.2]⟩
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg _) (by linarith only [hR] : 0 ≤ R)).mpr ha
  have hf := fun x hx => circleHeight_hasDerivAt (hinside x hx)
  have hg := fun x hx => circleHeight_first_hasDerivAt (hinside x hx)
  have hi : ContinuousOn (fun x => -(x-c)/circleHeight R c x) (Icc a (a+N)) :=
    fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hj : ContinuousOn (fun x => -(R^2)/circleHeight R c x^3) (Icc a (a+N)) := by
    apply continuousOn_const.div
    · have hc : Continuous (circleHeight R c) := by unfold circleHeight; fun_prop
      exact hc.continuousOn.pow 3
    · intro x hx
      exact pow_ne_zero 3 (circleHeight_pos (hinside x hx)).ne'
  have hb := abs_trapezoid_sum_sub_integral_le (circleHeight R c)
    (fun x => -(x-c)/circleHeight R c x) (fun x => -(R^2)/circleHeight R c x^3)
    a N hf hg hi hj (fun x hx => div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg R)) (pow_nonneg (Real.sqrt_nonneg _) 3))
  apply hb.trans
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hsa := abs_circleHeight_slope_le_sqrt hR hl (by linarith only [hr,hN])
  have hsb := abs_circleHeight_slope_le_sqrt hR (by linarith only [hl,hN]) hr
  have hsa' := le_abs_self (-(a-c)/circleHeight R c a)
  have hsb' := neg_abs_le (-(a+N-c)/circleHeight R c (a+N))
  linarith only [hsa,hsb,hsa',hsb']

/-- The area of a left tip region of width at most two is `O(sqrt R)`. -/
theorem abs_integral_circleHeight_left_tip_le {R c a : ℝ} (hR : 0 ≤ R)
    (hl : c-R ≤ a) (hr : a ≤ c-R+2) :
    |∫ x in c-R..a, circleHeight R c x| ≤ 4 * Real.sqrt R := by
  have hb := norm_integral_le_of_norm_le_const
    (a := c-R) (b := a) (C := 2 * Real.sqrt R) (f := circleHeight R c)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ circleHeight R c x from Real.sqrt_nonneg _)]
      apply circleHeight_le_two_sqrt_of_left_tip hR
      rw [uIoc_of_le hl] at hx
      exact hx.2.trans hr)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hl)] at hb
  have hw : a-(c-R) ≤ 2 := by linarith only [hr]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 2 * Real.sqrt R)
  linarith only [hb,hm]

/-- The same area bound for a right tip region of width at most two. -/
theorem abs_integral_circleHeight_right_tip_le {R c a : ℝ} (hR : 0 ≤ R)
    (hl : c+R-2 ≤ a) (hr : a ≤ c+R) :
    |∫ x in a..c+R, circleHeight R c x| ≤ 4 * Real.sqrt R := by
  have hb := norm_integral_le_of_norm_le_const
    (a := a) (b := c+R) (C := 2 * Real.sqrt R) (f := circleHeight R c)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ circleHeight R c x from Real.sqrt_nonneg _)]
      apply circleHeight_le_two_sqrt_of_right_tip hR
      rw [uIoc_of_le hr] at hx
      exact hl.trans hx.1.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr)] at hb
  have hw : c+R-a ≤ 2 := by linarith only [hl]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 2 * Real.sqrt R)
  linarith only [hb,hm]

/-- A sample sum whose endpoints lie between one and two units from the circle
tips differs from the full semicircle area by at most `11 * sqrt R`. -/
theorem abs_middle_circle_sum_sub_area_le {R c a : ℝ} (N : ℕ) (hR : 1 ≤ R)
    (hl : c-R+1 ≤ a) (hl' : a ≤ c-R+2)
    (hr : a+N ≤ c+R-1) (hr' : c+R-2 ≤ a+N) :
    |(∑ k ∈ Finset.range (N+1), circleHeight R c (a+k)) - Real.pi*R^2/2| ≤
      11 * Real.sqrt R := by
  have hRp : 0 ≤ R := le_trans zero_le_one hR
  have he := abs_le.mp (abs_circle_trapezoid_sub_integral_le N hR hl hr)
  have hleft := abs_le.mp (abs_integral_circleHeight_left_tip_le hRp
    (by linarith only [hl]) hl')
  have hright := abs_le.mp (abs_integral_circleHeight_right_tip_le hRp hr'
    (by linarith only [hr]))
  have ha := circleHeight_le_two_sqrt_of_left_tip hRp hl'
  have hb := circleHeight_le_two_sqrt_of_right_tip hRp hr'
  have ha0 : 0 ≤ circleHeight R c a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ circleHeight R c (a+N) := Real.sqrt_nonneg _
  have hc : Continuous (circleHeight R c) := by unfold circleHeight; fun_prop
  have hadd := integral_add_adjacent_intervals (μ := volume) (hc.intervalIntegrable (c-R) a)
    (hc.intervalIntegrable a (a+N))
  have hadd' := integral_add_adjacent_intervals (μ := volume) (hc.intervalIntegrable (c-R) (a+N))
    (hc.intervalIntegrable (a+N) (c+R))
  rw [integral_circleHeight (by linarith only [hR] : 0 < R)] at hadd'
  apply abs_le.mpr
  constructor <;> linarith only [he.1,he.2,hleft.1,hleft.2,hright.1,hright.2,
    ha,hb,ha0,hb0,hadd,hadd',Real.sqrt_nonneg R]

/-- Including both outer samples still gives a square-root area error. The
sample endpoints lie within one unit of the two circle tips. -/
theorem abs_circle_sample_sum_sub_area_le {R c a : ℝ} (N : ℕ) (hR : 1 ≤ R)
    (hl : c-R ≤ a) (hl' : a ≤ c-R+1)
    (hr : a+N+2 ≤ c+R) (hr' : c+R-1 ≤ a+N+2) :
    |(∑ k ∈ Finset.range (N+3), circleHeight R c (a+k)) - Real.pi*R^2/2| ≤
      15 * Real.sqrt R := by
  have hm := abs_le.mp (abs_middle_circle_sum_sub_area_le (c := c) (a := a+1) N hR
    (by linarith only [hl]) (by linarith only [hl'])
    (by linarith only [hr]) (by linarith only [hr']))
  have ha := circleHeight_le_two_sqrt_of_left_tip (le_trans zero_le_one hR)
    (by linarith only [hl'] : a ≤ c-R+2)
  have hb := circleHeight_le_two_sqrt_of_right_tip (le_trans zero_le_one hR)
    (by linarith only [hr'] : c+R-2 ≤ a+(N:ℝ)+2)
  have ha0 : 0 ≤ circleHeight R c a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ circleHeight R c (a+N+2) := Real.sqrt_nonneg _
  have he : (∑ k ∈ Finset.range (N+3), circleHeight R c (a+k)) =
      (∑ k ∈ Finset.range (N+1), circleHeight R c (a+1+k)) +
        circleHeight R c a + circleHeight R c (a+N+2) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero, add_zero]
    have hshift (k : ℕ) : a+((k:ℝ)+1) = a+1+k := by ring
    simp_rw [hshift]
    congr 1
    congr 1
    ring
  rw [he]
  apply abs_le.mpr
  constructor <;> linarith only [hm.1,hm.2,ha,hb,ha0,hb0]

end WaveTurbulence.Counting
