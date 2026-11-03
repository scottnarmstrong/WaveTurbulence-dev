/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleCentralQuadrature
public import WaveTurbulence.Foundations.Counting.CircleHeightSum
import Mathlib.Tactic

/-!
# Clipped circular height sums

Clipping a semicircle at the inscribed-square height removes precisely its
central excess. The error of that excess is absolute, rather than growing
with the radius. All integer samples retain their actual real center.
-/

public section

namespace WaveTurbulence.Counting

/-- Height of a semicircle clipped at the inscribed-square cut. -/
@[expose] noncomputable def circleClippedHeight (R T c x : ℝ) : ℝ :=
  min T (circleHeight R c x)

/-- Outside the central square, the circular height is at most its cut. -/
theorem circleHeight_le_central_cut {R T c x : ℝ} (hT : 0 ≤ T)
    (hTR : 2*T^2 = R^2) (hx : T ≤ |x-c|) : circleHeight R c x ≤ T := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨hT,?_⟩
  have hs := (sq_le_sq₀ hT (abs_nonneg _)).mpr hx
  rw [sq_abs] at hs
  nlinarith only [hs,hTR]

/-- Exact removal of the central excess from each sample. -/
theorem circleClippedHeight_eq_sub_excess {R T c x : ℝ} (hT : 0 ≤ T)
    (hTR : 2*T^2 = R^2) :
    circleClippedHeight R T c x = circleHeight R c x-
      (if |x-c| ≤ T then circleHeight R c x-T else 0) := by
  unfold circleClippedHeight
  by_cases hx : |x-c| ≤ T
  · rw [ite_eq_left hx,min_eq_left (circle_central_height_ge hT hTR hx)]
    ring
  · rw [ite_eq_right hx,min_eq_right (circleHeight_le_central_cut hT hTR (le_of_not_ge hx)),sub_zero]

/-- Clipping removes the exact central integer interval, with no endpoint
rounding or extra boundary samples. -/
theorem sum_circleClippedHeight_eq {R T c : ℝ} (hT : 0 ≤ T)
    (hTR : 2*T^2 = R^2) (hTRle : T ≤ R) :
    (∑ x ∈ integerInterval (c-R) (c+R), circleClippedHeight R T c x) =
      (∑ x ∈ integerInterval (c-R) (c+R), circleHeight R c x)-
      ∑ x ∈ integerInterval (c-T) (c+T), (circleHeight R c x-T) := by
  classical
  have he : (integerInterval (c-R) (c+R)).filter (fun x : ℤ => |(x:ℝ)-c| ≤ T) =
      integerInterval (c-T) (c+T) := by
    ext x
    simp only [Finset.mem_filter,mem_integerInterval,abs_le]
    constructor
    · rintro ⟨_,hx1,hx2⟩
      constructor <;> linarith only [hx1,hx2]
    · rintro ⟨hx1,hx2⟩
      constructor
      · constructor <;> linarith only [hx1,hx2,hTRle]
      · constructor <;> linarith only [hx1,hx2]
  simp_rw [circleClippedHeight_eq_sub_excess hT hTR]
  rw [Finset.sum_sub_distrib,← Finset.sum_filter,he]

/-- The central excess has uniformly bounded error on its actual integer
sample interval, whenever the cut height is at least one. -/
theorem abs_integer_central_excess_sum_sub_integral_le {R T c : ℝ}
    (hT : 1 ≤ T) (hTR : 2*T^2 = R^2) :
    |(∑ x ∈ integerInterval (c-T) (c+T), (circleHeight R c x-T))-
      (∫ x in c-T..c+T, (circleHeight R c x-T))| ≤ 4 := by
  let L : ℤ := ⌈c-T⌉
  let U : ℤ := ⌊c+T⌋
  have hL : c-T ≤ (L:ℝ) := Int.le_ceil _
  have hL' : (L:ℝ) < c-T+1 := Int.ceil_lt_add_one _
  have hU : (U:ℝ) ≤ c+T := Int.floor_le _
  have hU' : c+T-1 < (U:ℝ) := Int.sub_one_lt_floor _
  have hLU : L ≤ U := by
    have he : (L:ℝ) ≤ (U:ℝ) := by linarith only [hL',hU',hT]
    exact_mod_cast he
  let N : ℕ := (U-L).toNat
  have hN : (N:ℤ) = U-L := Int.toNat_of_nonneg (by omega)
  have hNR : (N:ℝ) = (U:ℝ)-(L:ℝ) := by exact_mod_cast hN
  have he : (L:ℝ)+N = U := by linarith only [hNR]
  have hM : (U+1-L).toNat = N+1 := by omega
  change |(∑ x ∈ Finset.Icc L U, (circleHeight R c x-T))-
    (∫ x in c-T..c+T, (circleHeight R c x-T))| ≤ 4
  rw [sum_int_Icc_eq_range (fun x : ℝ => circleHeight R c x-T),hM]
  apply abs_central_excess_sample_sum_sub_integral_le N
    (by linarith only [hT]) hTR hL hL'.le
  · rw [he]; exact hU
  · rw [he]; exact hU'.le

/-- The clipped sum inherits the original square-root quadrature bound,
with an additional absolute error of four. -/
theorem abs_integer_clippedHeight_sum_sub_integral_le {R T c : ℝ}
    (hR : 2 ≤ R) (hT : 1 ≤ T) (hTR : 2*T^2 = R^2) (hTRle : T ≤ R) :
    |(∑ x ∈ integerInterval (c-R) (c+R), circleClippedHeight R T c x)-
      (Real.pi*R^2/2-(∫ x in c-T..c+T, (circleHeight R c x-T)))| ≤
        15*Real.sqrt R+4 := by
  rw [sum_circleClippedHeight_eq (by linarith only [hT]) hTR hTRle]
  have hh := abs_integer_circleHeight_sum_sub_area_le (c := c) hR
  have he := abs_integer_central_excess_sum_sub_integral_le (c := c) hT hTR
  have halg : (∑ x ∈ integerInterval (c-R) (c+R), circleHeight R c x)-
      (∑ x ∈ integerInterval (c-T) (c+T), (circleHeight R c x-T))-
      (Real.pi*R^2/2-(∫ x in c-T..c+T, (circleHeight R c x-T))) =
      ((∑ x ∈ integerInterval (c-R) (c+R), circleHeight R c x)-Real.pi*R^2/2)-
      ((∑ x ∈ integerInterval (c-T) (c+T), (circleHeight R c x-T))-
        (∫ x in c-T..c+T, (circleHeight R c x-T))) := by ring
  rw [halg]
  exact (abs_sub _ _).trans (add_le_add hh he)

end WaveTurbulence.Counting
