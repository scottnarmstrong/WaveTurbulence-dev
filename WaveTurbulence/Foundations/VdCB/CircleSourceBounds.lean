/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleSourceCalculus

/-!
# Uniform source-derivative bounds on circle dyadic blocks

No small perturbation assumption is used. The entire arc factor is
retained in the actual second and third derivatives.
-/

public section

open Set

namespace WaveTurbulence.VdCB

private theorem circle_dyadic_height_bounds {R U u : ℝ} (hU : 0 < U) (hUR : 3 * U ≤ R)
    (hu : u ∈ Icc U (2 * U)) :
    R * U ≤ 2 * R * u - u ^ 2 ∧ 2 * R * u - u ^ 2 ≤ 4 * R * U := by
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  have hu0 := hU.trans_le hu.1
  constructor
  · have h1 := mul_le_mul_of_nonneg_left (show R ≤ 2 * R - u by linarith [hu.2]) hu0.le
    have h2 := mul_le_mul_of_nonneg_left hu.1 hR.le
    nlinarith only [h1, h2]
  · have hh := mul_le_mul_of_nonneg_left hu.2 (by positivity : 0 ≤ 2 * R)
    nlinarith only [hh, sq_nonneg u]

/-- Source curvature is negative and uniformly comparable with the
square-root scale on a full dyadic block. -/
theorem neg_deriv_deriv_circlePhase_bounds {R h U u : ℝ} (hU : 0 < U)
    (hUR : 3 * U ≤ R) (hh : 0 < h) (hu : u ∈ Icc U (2 * U)) :
    h * R ^ 2 * (4 * R * U) ^ (-(3 / 2) : ℝ) ≤ -deriv (deriv (circlePhase R h)) u ∧
      -deriv (deriv (circlePhase R h)) u ≤ h * R ^ 2 * (R * U) ^ (-(3 / 2) : ℝ) := by
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  have huarc : u ∈ Ioo 0 R := ⟨hU.trans_le hu.1, by linarith [hu.2]⟩
  have hD := circle_dyadic_height_bounds hU hUR hu
  have hD0 : 0 < 2 * R * u - u ^ 2 := (mul_pos hR hU).trans_le hD.1
  rw [deriv_deriv_circlePhase hR huarc]
  simp only [circleSourceSecond, neg_mul, neg_neg]
  constructor
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hD0 hD.2 (by norm_num)) (by positivity)
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (mul_pos hR hU) hD.1 (by norm_num)) (by positivity)

/-- The actual source third derivative has the dyadic inverse-power bound. -/
theorem abs_iteratedDeriv_three_circlePhase_le {R h U u : ℝ} (hU : 0 < U)
    (hUR : 3 * U ≤ R) (hh : 0 < h) (hu : u ∈ Icc U (2 * U)) :
    |iteratedDeriv 3 (circlePhase R h) u| ≤
      3 * h * R ^ 3 * (R * U) ^ (-(5 / 2) : ℝ) := by
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  have huarc : u ∈ Ioo 0 R := ⟨hU.trans_le hu.1, by linarith [hu.2]⟩
  have hD := circle_dyadic_height_bounds hU hUR hu
  have hD0 : 0 < 2 * R * u - u ^ 2 := (mul_pos hR hU).trans_le hD.1
  rw [iteratedDeriv_three_circlePhase hR huarc]
  have hRu : 0 ≤ R - u := sub_nonneg.mpr huarc.2.le
  have hn : 0 ≤ circleSourceThird R h u := by
    unfold circleSourceThird
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hD0.le _)
  rw [abs_of_nonneg hn]
  unfold circleSourceThird
  have h1 : 3 * h * R ^ 2 * (R - u) ≤ 3 * h * R ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left (show R - u ≤ R by linarith [huarc.1])
      (by positivity : 0 ≤ 3 * h * R ^ 2)
    convert hh using 1; ring
  exact mul_le_mul h1
    (Real.rpow_le_rpow_of_nonpos (mul_pos hR hU) hD.1 (by norm_num))
    (Real.rpow_nonneg hD0.le _) (by positivity)

end WaveTurbulence.VdCB
