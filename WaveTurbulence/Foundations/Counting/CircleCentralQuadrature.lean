/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleCentralArc
import Mathlib.Tactic

/-!
# Quadrature of the central excess

The excess of the circular arc over the inscribed-square height has an
absolute quadrature error, uniformly in the real center and radius.
-/

public section

namespace WaveTurbulence.Counting

open MeasureTheory intervalIntegral Set

theorem circleHeight_at_central_left {R T c : ℝ} (hT : 0 ≤ T)
    (hTR : 2*T^2 = R^2) : circleHeight R c (c-T) = T := by
  unfold circleHeight
  have he : R^2-(c-T-c)^2 = T^2 := by nlinarith only [hTR]
  rw [he,Real.sqrt_sq hT]

theorem circleHeight_at_central_right {R T c : ℝ} (hT : 0 ≤ T)
    (hTR : 2*T^2 = R^2) : circleHeight R c (c+T) = T := by
  unfold circleHeight
  have he : R^2-(c+T-c)^2 = T^2 := by nlinarith only [hTR]
  rw [he,Real.sqrt_sq hT]

/-- A central-excess tip of width at most one has integral at most one. -/
theorem abs_integral_central_excess_left_le {R T c a : ℝ} (hT : 0 < T)
    (hTR : 2*T^2 = R^2) (ha : c-T ≤ a) (ha' : a ≤ c-T+1) (haT : a ≤ c+T) :
    |∫ x in c-T..a, (circleHeight R c x-T)| ≤ 1 := by
  have he := norm_integral_le_of_norm_le_const (a := c-T) (b := a) (C := (1:ℝ))
    (f := fun x => circleHeight R c x-T) (fun x hx => by
      rw [uIoc_of_le ha] at hx
      have hb := abs_circle_central_height_sub_le hT hTR
        (show c-T ∈ Icc (c-T) (c+T) from ⟨le_rfl,by linarith only [hT]⟩)
        (show x ∈ Icc (c-T) (c+T) from ⟨hx.1.le,hx.2.trans haT⟩)
      rw [circleHeight_at_central_left hT.le hTR] at hb
      rw [Real.norm_eq_abs]
      have hx0 : 0 ≤ x-(c-T) := by linarith only [hx.1]
      exact hb.trans (by
        rw [abs_of_nonneg hx0]
        linarith only [hx.2,ha']))
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ha),one_mul] at he
  exact he.trans (by linarith only [ha'])

/-- The reflected central-excess tip estimate. -/
theorem abs_integral_central_excess_right_le {R T c b : ℝ} (hT : 0 < T)
    (hTR : 2*T^2 = R^2) (hb : b ≤ c+T) (hb' : c+T-1 ≤ b) (hbT : c-T ≤ b) :
    |∫ x in b..c+T, (circleHeight R c x-T)| ≤ 1 := by
  have he := norm_integral_le_of_norm_le_const (a := b) (b := c+T) (C := (1:ℝ))
    (f := fun x => circleHeight R c x-T) (fun x hx => by
      rw [uIoc_of_le hb] at hx
      have hc := abs_circle_central_height_sub_le hT hTR
        (show c+T ∈ Icc (c-T) (c+T) from ⟨by linarith only [hT],le_rfl⟩)
        (show x ∈ Icc (c-T) (c+T) from ⟨hbT.trans hx.1.le,hx.2⟩)
      rw [circleHeight_at_central_right hT.le hTR] at hc
      rw [Real.norm_eq_abs]
      have hx0 : x-(c+T) ≤ 0 := by linarith only [hx.2]
      exact hc.trans (by
        rw [abs_of_nonpos hx0]
        linarith only [hx.1,hb']))
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hb),one_mul] at he
  exact he.trans (by linarith only [hb'])

/-- Central samples within one unit of both cuts have quadrature error at
most four. Subtracting this excess preserves square-root circle quadrature. -/
theorem abs_central_excess_sample_sum_sub_integral_le {R T c a : ℝ} (N : ℕ)
    (hT : 0 < T) (hTR : 2*T^2 = R^2)
    (hl : c-T ≤ a) (hl' : a ≤ c-T+1)
    (hr : a+N ≤ c+T) (hr' : c+T-1 ≤ a+N) :
    |(∑ k ∈ Finset.range (N+1), (circleHeight R c (a+k)-T))-
      (∫ x in c-T..c+T, (circleHeight R c x-T))| ≤ 4 := by
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have he := abs_le.mp (abs_circle_central_trapezoid_error_le N hT hTR hl hr)
  have hleft := abs_le.mp (abs_integral_central_excess_left_le hT hTR hl hl'
    (by linarith only [hr,hN]))
  have hright := abs_le.mp (abs_integral_central_excess_right_le hT hTR hr hr'
    (by linarith only [hl,hN]))
  have hla : c-T ∈ Icc (c-T) (c+T) := ⟨le_rfl,by linarith only [hT]⟩
  have hra : c+T ∈ Icc (c-T) (c+T) := ⟨by linarith only [hT],le_rfl⟩
  have ha := abs_circle_central_height_sub_le hT hTR hla
    (show a ∈ Icc (c-T) (c+T) from ⟨hl,by linarith only [hr,hN]⟩)
  have hb := abs_circle_central_height_sub_le hT hTR hra
    (show a+N ∈ Icc (c-T) (c+T) from ⟨by linarith only [hl,hN],hr⟩)
  rw [circleHeight_at_central_left hT.le hTR] at ha
  rw [circleHeight_at_central_right hT.le hTR] at hb
  rw [abs_of_nonneg (sub_nonneg.mpr hl)] at ha
  rw [abs_of_nonpos (by linarith only [hr] : a+N-(c+T) ≤ 0)] at hb
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc : Continuous (fun x => circleHeight R c x-T) := by unfold circleHeight; fun_prop
  have hi := integral_add_adjacent_intervals (μ := volume) (hc.intervalIntegrable (c-T) a)
    (hc.intervalIntegrable a (a+N))
  have hj := integral_add_adjacent_intervals (μ := volume) (hc.intervalIntegrable (c-T) (a+N))
    (hc.intervalIntegrable (a+N) (c+T))
  apply abs_le.mpr
  constructor <;> linarith only [he.1,he.2,hleft.1,hleft.2,hright.1,hright.2,
    ha'.1,ha'.2,hb'.1,hb'.2,hl',hr',hi,hj]

end WaveTurbulence.Counting
