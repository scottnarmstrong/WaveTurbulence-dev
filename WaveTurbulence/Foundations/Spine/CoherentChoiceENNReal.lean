/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentChoiceAbsorption
public import Mathlib.Analysis.Normed.Group.Basic
/-! ENNReal form of the explicit finite choice-count absorption. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open scoped ENNReal

theorem coherent_choice_cost_le {d m A n : ℕ} (G : Garden 2) (hp : G.IsPlain) (ho : G.order = 2 * n)
    (C C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hchoice : ((inputLeaves G).card + 1 : ℝ) ^ A *
      (Fintype.card (RootWeightChoices G d m) : ℝ) ≤ C * 8 ^ n) :
    ((((inputLeaves G).card + 1 : ℕ) : ℝ≥0∞) ^ A *
      (Fintype.card (RootWeightChoices G d m) : ℝ≥0∞) *
      ENNReal.ofReal (C₁ ^ (inputLeaves G).card * C₂ ^ (4 * m + A))) ≤
      ENNReal.ofReal (C * 8 ^ n * (C₁ ^ (2 * n + 1) * C₂ ^ (4 * m + A))) := by
  have hcast : ((((inputLeaves G).card + 1 : ℕ) : ℝ≥0∞) ^ A *
      (Fintype.card (RootWeightChoices G d m) : ℝ≥0∞)) =
      ENNReal.ofReal (((inputLeaves G).card + 1 : ℝ) ^ A *
        (Fintype.card (RootWeightChoices G d m) : ℝ)) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    rw [ENNReal.ofReal_pow (by positivity)]
    simp only [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one, Nat.cast_add, Nat.cast_one]
  rw [hcast, ← ENNReal.ofReal_mul (by positivity), card_inputLeaves_couple G hp ho]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by simpa only [card_inputLeaves_couple G hp ho] using hchoice) (by positivity)

end WaveTurbulence.LGSpine
