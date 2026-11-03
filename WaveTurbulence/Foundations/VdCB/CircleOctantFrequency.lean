/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleFrequencyBounds

/-!
# Circle source frequencies on the octant arc

The exact octant cutoff supplies `ν≥h` and the quantitative dyadic
frequency bounds, including a dyadic block clipped by that cutoff.
-/

public section

open Set

namespace WaveTurbulence.VdCB

theorem circle_octant_factor_le_third : (1 : ℝ) - 1 / Real.sqrt 2 ≤ 1 / 3 := by
  have hs0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt (2 : ℝ) ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hh : (2 / 3 : ℝ) ≤ 1 / Real.sqrt 2 := (le_div_iff₀ hs0).mpr (by nlinarith only [hs])
  linarith only [hh]

/-- The actual octant arc lies in `u≤R/3`. -/
theorem three_mul_le_of_circle_octant {R u : ℝ} (hR : 0 ≤ R)
    (hu : u ≤ R * (1 - 1 / Real.sqrt 2)) : 3 * u ≤ R := by
  have hh := mul_le_mul_of_nonneg_left circle_octant_factor_le_third hR
  nlinarith only [hu, hh]

/-- Every actual octant source derivative is at least the frequency h. -/
theorem le_circleSourceFirst_of_octant {R h u : ℝ} (hR : 0 < R) (hh : 0 < h)
    (hu : u ∈ Ioo 0 R) (hoct : u ≤ R * (1 - 1 / Real.sqrt 2)) :
    h ≤ circleSourceFirst R h u := by
  have hs0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hRu : R / Real.sqrt 2 ≤ R - u := by
    rw [div_eq_mul_inv]
    have hO := hoct
    rw [one_div] at hO
    nlinarith only [hO]
  have hmul := (div_le_iff₀ hs0).mp hRu
  have hsq := pow_le_pow_left₀ hR.le hmul 2
  rw [mul_pow, hs2] at hsq
  have hD : 0 < 2 * R * u - u ^ 2 := by nlinarith only [hR, hu.1, hu.2]
  have hroot : Real.sqrt (2 * R * u - u ^ 2) ≤ R - u :=
    Real.sqrt_le_iff.mpr ⟨(sub_pos.mpr hu.2).le, by nlinarith only [hsq]⟩
  have hratio : 1 ≤ (R - u) / Real.sqrt (2 * R * u - u ^ 2) :=
    (one_le_div₀ (Real.sqrt_pos.mpr hD)).mpr hroot
  rw [circleSourceFirst_eq_div hR hu]
  calc
    h = h * 1 := by ring
    _ ≤ h * ((R - u) / Real.sqrt (2 * R * u - u ^ 2)) := mul_le_mul_of_nonneg_left hratio hh.le
    _ = _ := by ring

/-- The direct frequency comparisons cover also the clipped final dyadic block. -/
theorem circleSourceFirst_sq_bounds_of_octant {R h U u : ℝ} (hU : 0 < U)
    (hUR : 3 * U ≤ R) (hu : u ∈ Icc U (2 * U))
    (hoct : u ≤ R * (1 - 1 / Real.sqrt 2)) :
    h ^ 2 * R / (9 * U) ≤ (circleSourceFirst R h u) ^ 2 ∧
      (circleSourceFirst R h u) ^ 2 ≤ h ^ 2 * R / U := by
  have hR : 0 ≤ R := (by positivity : 0 < 3 * U).le.trans hUR
  exact circleSourceFirst_sq_bounds_of_arc hU hUR hu (three_mul_le_of_circle_octant hR hoct)

end WaveTurbulence.VdCB
