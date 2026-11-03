/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleSourceBounds

/-!
# Circle dual frequency scales from the actual source derivative

The squared frequency lies between `h²R/(9U)` and `h²R/U` on a dyadic
source block. These bounds retain the full arc factor and imply a fixed
ratio between the endpoint frequencies.
-/

public section

open Set

namespace WaveTurbulence.VdCB

theorem circleSourceFirst_eq_div {R h u : ℝ} (hR : 0 < R) (hu : u ∈ Ioo 0 R) :
    circleSourceFirst R h u = h * (R - u) / Real.sqrt (2 * R * u - u ^ 2) :=
  (hasDerivAt_circlePhase_rpow (h := h) hR hu).unique (hasDerivAt_circlePhase hR hu)

theorem circleSourceFirst_pos {R h u : ℝ} (hR : 0 < R) (hh : 0 < h) (hu : u ∈ Ioo 0 R) :
    0 < circleSourceFirst R h u := by
  rw [circleSourceFirst_eq_div hR hu]
  apply div_pos (mul_pos hh (sub_pos.mpr hu.2))
  exact Real.sqrt_pos.mpr (by nlinarith only [hR, hu.1, hu.2])

private theorem source_first_sq {R h u : ℝ} (hR : 0 < R) (hu : u ∈ Ioo 0 R) :
    (circleSourceFirst R h u) ^ 2 = h ^ 2 * (R - u) ^ 2 / (2 * R * u - u ^ 2) := by
  rw [circleSourceFirst_eq_div hR hu, div_pow, mul_pow,
    Real.sq_sqrt (by nlinarith only [hR, hu.1, hu.2])]

/-- Exact squared dual-frequency comparison on a dyadic block. -/
theorem circleSourceFirst_sq_bounds_of_arc {R h U u : ℝ} (hU : 0 < U) (hUR : 3 * U ≤ R)
    (hu : u ∈ Icc U (2 * U)) (hu3 : 3 * u ≤ R) :
    h ^ 2 * R / (9 * U) ≤ (circleSourceFirst R h u) ^ 2 ∧
      (circleSourceFirst R h u) ^ 2 ≤ h ^ 2 * R / U := by
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  have huarc : u ∈ Ioo 0 R := ⟨hU.trans_le hu.1, by linarith [hu.2]⟩
  have hD : 0 < 2 * R * u - u ^ 2 := by nlinarith only [hR, huarc.1, huarc.2]
  have hDlo : R * U ≤ 2 * R * u - u ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (show R ≤ 2 * R - u by linarith [huarc.2]) huarc.1.le
    have h2 := mul_le_mul_of_nonneg_left hu.1 hR.le
    nlinarith only [h1, h2]
  have hDhi : 2 * R * u - u ^ 2 ≤ 4 * R * U := by
    have hh := mul_le_mul_of_nonneg_left hu.2 (by positivity : 0 ≤ 2 * R)
    nlinarith only [hh, sq_nonneg u]
  rw [source_first_sq hR huarc]
  constructor
  · apply (div_le_div_iff₀ (by positivity : 0 < 9 * U) hD).mpr
    have hlo : (2 * R / 3) ^ 2 ≤ (R - u) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hu3]) 2
    have h1 := mul_le_mul_of_nonneg_left hDhi hR.le
    have h2 := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 9 * U)
    have hbase : R * (2 * R * u - u ^ 2) ≤ (9 * U) * (R - u) ^ 2 := by
      nlinarith only [h1, h2]
    convert mul_le_mul_of_nonneg_left hbase (sq_nonneg h) using 1 <;> ring
  · apply (div_le_div_iff₀ hD hU).mpr
    have hlo : (R - u) ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ (sub_nonneg.mpr huarc.2.le) (by linarith [huarc.1]) 2
    have h1 := mul_le_mul_of_nonneg_right hlo hU.le
    have h2 := mul_le_mul_of_nonneg_left hDlo hR.le
    have hbase : (R - u) ^ 2 * U ≤ R * (2 * R * u - u ^ 2) := by nlinarith only [h1, h2]
    convert mul_le_mul_of_nonneg_left hbase (sq_nonneg h) using 1 <;> ring

/-- The full dyadic-block version follows from `6U≤R`. -/
theorem circleSourceFirst_sq_bounds {R h U u : ℝ} (hU : 0 < U) (hUR : 6 * U ≤ R)
    (hu : u ∈ Icc U (2 * U)) :
    h ^ 2 * R / (9 * U) ≤ (circleSourceFirst R h u) ^ 2 ∧
      (circleSourceFirst R h u) ^ 2 ≤ h ^ 2 * R / U := by
  exact circleSourceFirst_sq_bounds_of_arc hU (by linarith only [hUR, hU]) hu
    (by linarith only [hUR, hu.2])

/-- Only a fixed number of dual dyadic blocks is needed for one source block. -/
theorem circleSourceFirst_U_le_three_twoU {R h U : ℝ} (hU : 0 < U)
    (hUR : 6 * U ≤ R) (hh : 0 < h) :
    circleSourceFirst R h U ≤ 3 * circleSourceFirst R h (2 * U) := by
  have hR : 0 < R := (by positivity : 0 < 6 * U).trans_le hUR
  have hlow := (circleSourceFirst_sq_bounds (h := h) hU hUR (show 2 * U ∈ Icc U (2 * U) by constructor <;> linarith)).1
  have hhigh := (circleSourceFirst_sq_bounds (h := h) hU hUR (show U ∈ Icc U (2 * U) by constructor <;> linarith)).2
  have hsq : (circleSourceFirst R h U) ^ 2 ≤ 9 * (circleSourceFirst R h (2 * U)) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hlow (by norm_num : (0 : ℝ) ≤ 9)
    have heq : 9 * (h ^ 2 * R / (9 * U)) = h ^ 2 * R / U := by ring
    rw [heq] at hh
    exact hhigh.trans hh
  have hp1 := circleSourceFirst_pos hR hh (show U ∈ Ioo 0 R by constructor <;> linarith)
  have hp2 := circleSourceFirst_pos hR hh (show 2 * U ∈ Ioo 0 R by constructor <;> linarith)
  nlinarith only [hsq, hp1, hp2]

end WaveTurbulence.VdCB
