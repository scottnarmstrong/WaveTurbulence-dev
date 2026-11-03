/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleScaleComparison

/-! # Scalar bounds for short source intervals -/

public section

namespace WaveTurbulence.VdCB

/-- The reciprocal curvature scale is one of the optimized error monomials. -/
theorem inv_sqrt_circleCurvatureLower_le {R h U : ℝ} (hR : 0 < R) (hh : 0 < h)
    (hU : 0 < U) :
    1 / Real.sqrt (circleCurvatureLower R h U) ≤
      3 * U / Real.sqrt (circleOscillation R h U) := by
  let F := circleOscillation R h U
  have hF : 0 < F := by dsimp only [F, circleOscillation]; positivity
  rw [circleCurvatureLower_eq hR hU]
  let t := Real.sqrt (F / (8 * U ^ 2))
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t ^ 2 = F / (8 * U ^ 2) := Real.sq_sqrt (by positivity)
  have hs : (3 * U * t) ^ 2 = (9 / 8 : ℝ) * F := by
    calc
      _ = 9 * U ^ 2 * t ^ 2 := by ring
      _ = _ := by rw [ht2]; field_simp
  have hbound : Real.sqrt F ≤ 3 * U * t := by
    nlinarith only [hs, Real.sq_sqrt hF.le, hF.le,
      Real.sqrt_nonneg F, mul_pos (by positivity : 0 < 3 * U) ht]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hF)).mpr
  calc
    1 / t * Real.sqrt F = Real.sqrt F / t := by ring
    _ ≤ 3 * U := (div_le_iff₀ ht).mpr (by nlinarith only [hbound])

/-- The chosen source radius times square-root curvature is small. -/
theorem circle_radius_mul_sqrt_curvature_le {R h U : ℝ} (hR : 0 < R)
    (hU : 1 ≤ U) (hUF : U ≤ circleOscillation R h U) :
    (U / circleOscillation R h U ^ (2 / 5 : ℝ)) *
      Real.sqrt (circleCurvatureLower R h U) ≤ circleOscillation R h U ^ (2 / 5 : ℝ) := by
  let F := circleOscillation R h U
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hF1 : 1 ≤ F := hU.trans hUF
  have hF : 0 < F := zero_lt_one.trans_le hF1
  have hP : 0 < F ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos hF _
  rw [circleCurvatureLower_eq hR hU0]
  have hs : Real.sqrt (F / (8 * U ^ 2)) ≤ Real.sqrt F / U := by
    have he : Real.sqrt F / U = Real.sqrt (F / U ^ 2) := by
      rw [Real.sqrt_div hF.le, Real.sqrt_sq_eq_abs, abs_of_pos hU0]
    rw [he]
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left hF.le (sq_pos_of_pos hU0) (by nlinarith only [sq_nonneg U])
  have hp : Real.sqrt F ≤ (F ^ (2 / 5 : ℝ)) ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hF.le]
    exact Real.rpow_le_rpow_of_exponent_le hF1 (by norm_num)
  change U / F ^ (2 / 5 : ℝ) * Real.sqrt (F / (8 * U ^ 2)) ≤ _
  calc
    _ ≤ (U / F ^ (2 / 5 : ℝ)) * (Real.sqrt F / U) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = Real.sqrt F / F ^ (2 / 5 : ℝ) := by field_simp
    _ ≤ _ := (div_le_iff₀ hP).mpr (by nlinarith only [hp])

end WaveTurbulence.VdCB
