/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootWeightChoiceCount
public import WaveTurbulence.Foundations.Spine.InputLeafCount
/-! Finite weight and derivative choice counts cost one fixed constant and 8^n per couple. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

theorem exists_coherent_choice_bound (d m A : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (G : Garden 2), G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A *
        (Fintype.card (RootWeightChoices G d m) : ℝ) ≤ C * 8 ^ n := by
  obtain ⟨C₀, hC₀, hroot⟩ := exists_root_weight_choices_bound d m
  obtain ⟨C₁, hC₁, hpoly⟩ := exists_succ_pow_le_geometric A
  let C := (2 : ℝ) ^ A * C₁ * C₀ ^ 2
  have hC : 1 ≤ C := by
    dsimp [C]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hC₁) (one_le_pow₀ hC₀)
  refine ⟨C, hC, ?_⟩
  intro n G hp ho
  have hi : ((inputLeaves G).card + 1 : ℝ) = 2 * ((n : ℝ) + 1) := by
    rw [card_inputLeaves_couple G hp ho]
    push_cast
    ring
  rw [hi, mul_pow]
  have hr := hroot 2 G
  rw [ho] at hr
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_left (hpoly n) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) A)) hr
    (Nat.cast_nonneg _) (by positivity : 0 ≤ (2 : ℝ) ^ A * (C₁ * 2 ^ n))
  apply hh.trans_eq
  dsimp [C]
  rw [pow_mul]
  have he : (2 : ℝ) ^ n * ((2 : ℝ) ^ 2) ^ n = 8 ^ n := by
    rw [← mul_pow]
    norm_num
  calc
    _ = 2 ^ A * C₁ * C₀ ^ 2 * (2 ^ n * (2 ^ 2) ^ n) := by ring
    _ = _ := by rw [he]

end WaveTurbulence.LGSpine
