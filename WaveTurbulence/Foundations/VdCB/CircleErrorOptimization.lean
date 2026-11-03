/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleScaleIdentities

/-! # Explicit radius optimization for the circle B-process -/

public section

namespace WaveTurbulence.VdCB

/-- The optimized circle error is bounded by two elementary monomials. -/
theorem circleBError_optimized_le {R h U : ℝ} (hR : 0 < R)
    (hU : 1 ≤ U) (hUF : U ≤ circleOscillation R h U) :
    circleBError R h U
      (U / circleOscillation R h U ^ (2 / 5 : ℝ))
      (Real.sqrt (circleCurvatureLower R h U)) ≤
    (8 * Real.pi + 400) * (circleOscillation R h U ^ (2 / 5 : ℝ) +
      U / Real.sqrt (circleOscillation R h U)) := by
  let F := circleOscillation R h U
  let P := F ^ (2 / 5 : ℝ)
  let W := Real.sqrt F
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hF1 : 1 ≤ F := hU.trans hUF
  have hF : 0 < F := zero_lt_one.trans_le hF1
  have hP : 0 < P := Real.rpow_pos_of_pos hF _
  have hP1 : 1 ≤ P := Real.one_le_rpow hF1 (by norm_num)
  have hW : 0 < W := Real.sqrt_pos.mpr hF
  have hW2 : W ^ 2 = F := Real.sq_sqrt hF.le
  have hP5 : P ^ 5 = F ^ 2 := by
    dsimp only [P]
    rw [← Real.rpow_mul_natCast hF.le]
    norm_num
  have hFP : F ≤ P ^ 2 * W := by
    dsimp only [P, W]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hF.le, ← Real.rpow_add hF]
    convert Real.rpow_le_rpow_of_exponent_le hF1 (by norm_num : (1 : ℝ) ≤ 2 / 5 * 2 + 1 / 2) using 1
    rw [Real.rpow_one]
  let μ := F / (8 * U ^ 2)
  let t := Real.sqrt μ
  have hμ : 0 < μ := div_pos hF (by positivity)
  have ht : 0 < t := Real.sqrt_pos.mpr hμ
  have ht2 : t ^ 2 = μ := Real.sq_sqrt hμ.le
  have htlow : W / (3 * U) ≤ t := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * U)).mpr
    have he : (3 * U * t) ^ 2 = (9 / 8 : ℝ) * F := by
      dsimp only [μ] at ht2
      calc
        _ = 9 * U ^ 2 * t ^ 2 := by ring
        _ = _ := by rw [ht2]; field_simp
    nlinarith only [he, hW2, hF.le, mul_pos (by positivity : 0 < 3 * U) ht, hW.le]
  have hinv : 1 / t ≤ 3 * U / W := by
    apply (le_div_iff₀ hW).mpr
    have he := (div_le_iff₀ (by positivity : 0 < 3 * U)).mp htlow
    calc
      1 / t * W = W / t := by ring
      _ ≤ 3 * U := (div_le_iff₀ ht).mpr (by nlinarith only [he])
  have hsplit : 2 * t / μ + 2 / (Real.pi * t) ≤ 12 * U / W := by
    have hfirst : 2 * t / μ = 2 / t := by rw [← ht2]; field_simp
    have hsecond : 2 / (Real.pi * t) ≤ 2 / t := by
      apply div_le_div_of_nonneg_left (by norm_num) ht
      exact le_mul_of_one_le_left ht.le (by linarith only [Real.two_le_pi])
    rw [hfirst]
    simp only [div_eq_mul_inv] at hsecond hinv ⊢
    linarith only [hsecond, hinv]
  have hQ : F / U ^ 2 * U + 3 ≤ 4 * F / U := by
    have hh : 1 ≤ F / U := (one_le_div₀ hU0).mpr hUF
    have he : F / U ^ 2 * U = F / U := by field_simp
    rw [he]
    simp only [div_eq_mul_inv] at hh ⊢
    linarith only [hh]
  have hFPdiv : F / (P * W) ≤ P := by
    apply (div_le_iff₀ (mul_pos hP hW)).mpr
    nlinarith only [hFP]
  have homit : 2 * (F / U ^ 2 * (U / P) + 3) *
      (2 * t / μ + 2 / (Real.pi * t)) ≤ 24 * P + 72 * U / W := by
    calc
      _ ≤ 2 * (F / U ^ 2 * (U / P) + 3) * (12 * U / W) :=
        mul_le_mul_of_nonneg_left hsplit (by positivity)
      _ = 24 * (F / (P * W)) + 72 * U / W := by field_simp; ring
      _ ≤ _ := by linarith only [hFPdiv]
  have hstat : (F / U ^ 2 * U + 3) *
      (2 * Real.pi / 3 * (3 * F / U ^ 3) * (U / P) ^ 4 +
        4 / (Real.pi * (μ * (U / P)))) ≤ (8 * Real.pi + 128) * P := by
    have he : 4 * F / U *
        (2 * Real.pi / 3 * (3 * F / U ^ 3) * (U / P) ^ 4 +
          4 / (Real.pi * (μ * (U / P)))) =
        8 * Real.pi * (F ^ 2 / P ^ 4) + 128 / Real.pi * P := by
      dsimp only [μ]
      field_simp
      ring
    have hp : F ^ 2 / P ^ 4 = P := by rw [← hP5]; field_simp
    have hpi : 128 / Real.pi ≤ 128 := by
      apply (div_le_iff₀ Real.pi_pos).mpr
      linarith only [Real.two_le_pi]
    calc
      _ ≤ 4 * F / U *
          (2 * Real.pi / 3 * (3 * F / U ^ 3) * (U / P) ^ 4 +
            4 / (Real.pi * (μ * (U / P)))) := mul_le_mul_of_nonneg_right hQ (by positivity)
      _ = _ := he
      _ ≤ _ := by rw [hp]; nlinarith only [mul_le_mul_of_nonneg_right hpi hP.le]
  have hlog : Real.log (F / U ^ 2 * U + 3) ≤ 4 + (5 / 2 : ℝ) * P := by
    have hq4 : F / U ^ 2 * U + 3 ≤ 4 * F := by
      have hfu : F / U ≤ F := div_le_self hF.le hU
      have he : F / U ^ 2 * U = F / U := by field_simp
      rw [he]
      linarith only [hfu, hF1]
    have hqpos : 0 < F / U ^ 2 * U + 3 := by positivity
    have hl := Real.log_le_rpow_div hF.le (by norm_num : (0 : ℝ) < 2 / 5)
    have hl4 : Real.log 4 ≤ (4 : ℝ) := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    calc
      _ ≤ Real.log (4 * F) := Real.log_le_log hqpos hq4
      _ = Real.log 4 + Real.log F := Real.log_mul (by norm_num) hF.ne'
      _ ≤ _ := by dsimp only [P]; linarith only [hl, hl4]
  have hpoisson : (2 + 6 * Real.log (F / U ^ 2 * U + 3)) / (2 * Real.pi) + 1 ≤ 100 * P := by
    have hnum : 2 + 6 * Real.log (F / U ^ 2 * U + 3) ≤ 41 * P := by
      linarith only [hlog, hP1]
    have hdiv : (2 + 6 * Real.log (F / U ^ 2 * U + 3)) / (2 * Real.pi) ≤ 41 * P := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
      have hp := mul_le_mul_of_nonneg_right Real.two_le_pi hP.le
      nlinarith only [hnum, hp, hP.le]
    linarith only [hdiv, hP1]
  rw [circleBError, circleCurvatureUpper_eq hR hU0, circleCurvatureLower_eq hR hU0,
    circleThirdScale_eq hR hU0]
  change _ ≤ (8 * Real.pi + 400) * (P + U / W)
  change (2 + 6 * Real.log (F / U ^ 2 * U + 3)) / (2 * Real.pi) + 1 +
    2 * (F / U ^ 2 * (U / P) + 3) * (2 * t / μ + 2 / (Real.pi * t)) +
    (F / U ^ 2 * U + 3) * (2 * Real.pi / 3 * (3 * F / U ^ 3) * (U / P) ^ 4 +
      4 / (Real.pi * (μ * (U / P)))) ≤ _
  have hw0 : 0 ≤ U / W := (div_pos hU0 hW).le
  calc
    _ ≤ 100 * P + (24 * P + 72 * U / W) + (8 * Real.pi + 128) * P :=
      add_le_add (add_le_add hpoisson homit) hstat
    _ ≤ _ := by
      have hpw := mul_nonneg Real.pi_pos.le hw0
      simp only [div_eq_mul_inv] at hw0 hpw ⊢
      nlinarith only [hP.le, hw0, hpw]

end WaveTurbulence.VdCB
