/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleSourceScales
public import Mathlib.Tactic

/-! # Scalar identities for optimization of the direct circle B-process -/

public section

namespace WaveTurbulence.VdCB

/-- The dimensionless oscillation on a source block. -/
@[expose] noncomputable def circleOscillation (R h U : ℝ) : ℝ :=
  h * (R * U) ^ (1 / 2 : ℝ)

private theorem rpow_half_sub_nat {x : ℝ} (hx : 0 < x) (k : ℕ) :
    x ^ ((1 / 2 : ℝ) - k) = x ^ (1 / 2 : ℝ) / x ^ k := by
  rw [Real.rpow_sub hx, Real.rpow_natCast]

/-- The actual upper curvature in dimensionless variables. -/
theorem circleCurvatureUpper_eq {R h U : ℝ} (hR : 0 < R) (hU : 0 < U) :
    circleCurvatureUpper R h U = circleOscillation R h U / U ^ 2 := by
  unfold circleCurvatureUpper circleOscillation
  rw [show (-(3 / 2) : ℝ) = 1 / 2 - (2 : ℕ) by norm_num,
    rpow_half_sub_nat (mul_pos hR hU)]
  field_simp

/-- The lower curvature is one eighth of the upper curvature. -/
theorem circleCurvatureLower_eq {R h U : ℝ} (hR : 0 < R) (hU : 0 < U) :
    circleCurvatureLower R h U = circleOscillation R h U / (8 * U ^ 2) := by
  have hfour : (4 : ℝ) ^ (-(3 / 2) : ℝ) = 1 / 8 := by
    rw [show (-(3 / 2) : ℝ) = 1 / 2 - (2 : ℕ) by norm_num,
      rpow_half_sub_nat (by norm_num), ← Real.sqrt_eq_rpow]
    norm_num
  unfold circleCurvatureLower
  rw [mul_assoc 4 R U, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (mul_pos hR hU).le, hfour]
  have he := circleCurvatureUpper_eq (h := h) hR hU
  unfold circleCurvatureUpper at he
  rw [show h * R ^ 2 * (1 / 8 * (R * U) ^ (-(3 / 2) : ℝ)) =
    (h * R ^ 2 * (R * U) ^ (-(3 / 2) : ℝ)) / 8 by ring, he]
  ring

/-- The cubic scale in dimensionless variables. -/
theorem circleThirdScale_eq {R h U : ℝ} (hR : 0 < R) (hU : 0 < U) :
    circleThirdScale R h U = 3 * circleOscillation R h U / U ^ 3 := by
  unfold circleThirdScale circleOscillation
  rw [show (-(5 / 2) : ℝ) = 1 / 2 - (3 : ℕ) by norm_num,
    rpow_half_sub_nat (mul_pos hR hU)]
  field_simp

/-- The transformed source monomial is the standard `(11/30,16/30)` scale. -/
theorem circleBScale_eq {R h U : ℝ} (hR : 0 < R) (hh : 0 < h) (hU : 0 < U) :
    circleBScale R h U = circleOscillation R h U ^ (11 / 30 : ℝ) * U ^ (1 / 6 : ℝ) := by
  unfold circleBScale circleOscillation
  rw [Real.mul_rpow hh.le (Real.rpow_nonneg (mul_pos hR hU).le _),
    ← Real.rpow_mul (mul_pos hR hU).le,
    Real.mul_rpow hR.le hU.le]
  norm_num only [show (1 / 2 : ℝ) * (11 / 30) = 11 / 60 by norm_num]
  simp only [mul_assoc]
  rw [← Real.rpow_add hU]
  norm_num

/-- Every nontrivial harmonic and octant block has oscillation at least its length. -/
theorem le_circleOscillation {R h U : ℝ} (hU : 1 ≤ U) (hRU : U ≤ R) (hh : 1 ≤ h) :
    U ≤ circleOscillation R h U := by
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hRU0 : 0 ≤ R * U := mul_nonneg (hU0.trans hRU) hU0
  have hs : U ≤ (R * U) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt hU0 hRU0).mpr (by nlinarith only [mul_le_mul_of_nonneg_right hRU hU0])
  unfold circleOscillation
  exact hs.trans (le_mul_of_one_le_left (Real.rpow_nonneg hRU0 _) hh)

end WaveTurbulence.VdCB
