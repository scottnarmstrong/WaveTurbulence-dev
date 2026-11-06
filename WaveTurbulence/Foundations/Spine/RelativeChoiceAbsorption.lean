/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentChoiceENNReal
/-! Finite choice absorption preserves the marked baseline factor epsilon. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open scoped ENNReal

/-- The original low-order leaf product may carry an additional small factor.
It survives the full root-weight and derivative-choice enumeration. -/
theorem coherent_choice_cost_marked_le {d m A n : ℕ} (G : Garden 2)
    (hp : G.IsPlain) (ho : G.order = 2 * n) (C C₁ C₂ b ε : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hε : 0 ≤ ε)
    (hb : b ≤ ε * C₁ ^ (inputLeaves G).card)
    (hchoice : ((inputLeaves G).card + 1 : ℝ) ^ A *
      (Fintype.card (RootWeightChoices G d m) : ℝ) ≤ C * 8 ^ n) :
    ((((inputLeaves G).card + 1 : ℕ) : ℝ≥0∞) ^ A *
      (Fintype.card (RootWeightChoices G d m) : ℝ≥0∞) *
        ENNReal.ofReal (b * C₂ ^ (4 * m + A))) ≤
      ENNReal.ofReal (ε * (C * 8 ^ n * (C₁ ^ (2 * n + 1) * C₂ ^ (4 * m + A)))) := by
  let X : ℝ≥0∞ := (((inputLeaves G).card + 1 : ℕ) : ℝ≥0∞) ^ A *
    (Fintype.card (RootWeightChoices G d m) : ℝ≥0∞)
  have hfactor : ENNReal.ofReal (b * C₂ ^ (4 * m + A)) ≤
      ENNReal.ofReal ε * ENNReal.ofReal (C₁ ^ (inputLeaves G).card * C₂ ^ (4 * m + A)) := by
    rw [← ENNReal.ofReal_mul hε]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (ε * C₁ ^ (inputLeaves G).card) * C₂ ^ (4 * m + A) :=
        mul_le_mul_of_nonneg_right hb (pow_nonneg hC₂ _)
      _ = _ := by ring
  have hh := coherent_choice_cost_le G hp ho C C₁ C₂ hC₁ hC₂ hchoice
  change X * _ ≤ _ at hh ⊢
  calc
    _ ≤ X * (ENNReal.ofReal ε * ENNReal.ofReal
        (C₁ ^ (inputLeaves G).card * C₂ ^ (4 * m + A))) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = ENNReal.ofReal ε * (X * ENNReal.ofReal
        (C₁ ^ (inputLeaves G).card * C₂ ^ (4 * m + A))) := by ac_rfl
    _ ≤ ENNReal.ofReal ε * ENNReal.ofReal
        (C * 8 ^ n * (C₁ ^ (2 * n + 1) * C₂ ^ (4 * m + A))) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := (ENNReal.ofReal_mul hε).symm

end WaveTurbulence.LGSpine
