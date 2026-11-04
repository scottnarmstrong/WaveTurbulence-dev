/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Explicit interpolation exponents for incoherent regular objects

TARGET (incohproof24)–(incohproof28). The high endpoint loses `L^(4d)`;
its interpolation coefficient is `2η/(1/4+η)`, and the final loss fits
within `100dηg` for every incoherence count `g ≥ 1`.
-/

public section

noncomputable section

namespace WaveTurbulence.Incoh

/-- Weight of the quarter-derivative endpoint in the tree interpolation. -/
@[expose] def treeInterpolationWeight (η : ℝ) : ℝ := 2 * η / (1 / 4 + η)

theorem treeInterpolationWeight_pos {η : ℝ} (hη : 0 < η) :
    0 < treeInterpolationWeight η := by unfold treeInterpolationWeight; positivity

theorem treeInterpolationWeight_lt_one {η : ℝ} (hη : 0 ≤ η) (hη1 : η < 1 / 4) :
    treeInterpolationWeight η < 1 := by
  unfold treeInterpolationWeight
  apply (div_lt_one (by linarith only [hη])).2
  linarith only [hη1]

/-- The interpolated regularity is exactly the required positive exponent. -/
theorem treeInterpolationWeight_identity {η : ℝ} (hη : 0 ≤ η) :
    treeInterpolationWeight η * (1 / 4) + (1 - treeInterpolationWeight η) * (-η) = η := by
  have H : 1 / 4 + η ≠ 0 := ne_of_gt (by linarith only [hη])
  unfold treeInterpolationWeight
  field_simp
  ring

/-- The quarter-derivative endpoint enters with weight at most `8η`. -/
theorem treeInterpolationWeight_le_eight_mul {η : ℝ} (hη : 0 ≤ η) :
    treeInterpolationWeight η ≤ 8 * η := by
  unfold treeInterpolationWeight
  apply (div_le_iff₀ (by linarith only [hη])).2
  nlinarith only [sq_nonneg η]

/-- A fixed small-parameter range bounds the high endpoint's weight by one half. -/
theorem treeInterpolationWeight_le_half {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1 / 100) :
    treeInterpolationWeight η ≤ 1 / 2 := by
  unfold treeInterpolationWeight
  apply (div_le_iff₀ (by linarith only [hη])).2
  linarith only [hη1]

/-- Pure algebra for the final exponent; no norm estimate is an assumption here. -/
theorem tree_interpolation_loss_budget {D η G a : ℝ} (hD : 0 ≤ D) (hη : 0 ≤ η)
    (hG : 1 ≤ G) (ha : 0 ≤ a) (haHalf : a ≤ 1 / 2) (haη : a ≤ 8 * η) :
    (1 - a) * (2 * D * η * G) + a * (100 * D * η * G + 4 * D) ≤ 100 * D * η * G := by
  have hDG : 0 ≤ D * η * G := mul_nonneg (mul_nonneg hD hη) (zero_le_one.trans hG)
  have H₀ := mul_le_mul_of_nonneg_right (sub_le_self 1 ha) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hDG)
  have H₁ := mul_le_mul_of_nonneg_right haHalf (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hDG)
  have H₂ := mul_le_mul_of_nonneg_right haη (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hD)
  have H₃ := mul_le_mul_of_nonneg_left hG (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) (mul_nonneg hD hη))
  linarith only [H₀, H₁, H₂, H₃, hDG]

/-- The physical interpolation exponent costs at most `3η` powers of the pointwise scale. -/
theorem couple_interpolation_fraction_le {η : ℝ} (hη : 0 ≤ η) :
    1 - 1 / (1 + 3 * η) ≤ 3 * η := by
  have hp : 0 < 1 + 3 * η := by positivity
  have heq : 1 - 1 / (1 + 3 * η) = (3 * η) / (1 + 3 * η) := by
    field_simp
    ring
  rw [heq]
  exact div_le_self (by positivity) (by linarith)

/-- The L¹ loss and the physical interpolation loss together fit `8dηg`. -/
theorem couple_interpolation_loss_budget {D η G : ℝ} (hD : 1 ≤ D) (hη : 0 ≤ η) (hG : 1 ≤ G) :
    2 * η * G + (2 * D) * (1 - 1 / (1 + 3 * η)) ≤ 8 * D * η * G := by
  have hD₀ := zero_le_one.trans hD
  have hG₀ := zero_le_one.trans hG
  have h₁ := mul_le_mul_of_nonneg_left (couple_interpolation_fraction_le hη)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD₀)
  have h₂ := mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 6 * D * η)
  have h₃ := mul_le_mul_of_nonneg_right hD (mul_nonneg hη hG₀)
  linarith only [h₁, h₂, h₃]

end WaveTurbulence.Incoh
