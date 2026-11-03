/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.GainTrilinear
public import WaveTurbulence.Foundations.WKEL2.LossTwoTrilinear
public import WaveTurbulence.Foundations.WKEL2.LossThreeTrilinear

/-!
# The general-d weighted L² trilinear estimate

Theorem 7 of `docs/research/git20-general-d.md`, corresponding to TARGET
(C.8), for every d ≥ 3 and s > d/2 - 1. The norm is exactly the frozen
`weightedL2Norm`, and genuine weighted L² membership is part of the result.
The signed theorem includes all nonnegative Borel inputs.
-/

public section

noncomputable section

open MeasureTheory

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Research-note Theorem 7: all four signed collision terms are bounded on the exact weighted L² space. -/
theorem exists_collisionTerm_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : Fin 4, ∀ f₁ f₂ f₃ : Mom d → ℝ,
      Measurable f₁ → Measurable f₂ → Measurable f₃ →
      MemLp (weightedFunction s f₁) 2 → MemLp (weightedFunction s f₂) 2 →
      MemLp (weightedFunction s f₃) 2 →
      MemLp (weightedFunction s (collisionTerm j f₁ f₂ f₃)) 2 ∧
      weightedL2Norm s (collisionTerm j f₁ f₂ f₃) ≤
        C * weightedL2Norm s f₁ * weightedL2Norm s f₂ * weightedL2Norm s f₃ := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_collisionTerm_zero_bound hd s hs
  obtain ⟨C₁, hC₁, h₁⟩ := exists_collisionTerm_one_bound hd s hs
  obtain ⟨C₂, hC₂, h₂⟩ := exists_collisionTerm_two_bound hd s hs
  obtain ⟨C₃, hC₃, h₃⟩ := exists_collisionTerm_three_bound hd s hs
  let C := C₀ + C₁ + C₂ + C₃
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hc₀ : C₀ ≤ C := by dsimp only [C]; linarith only [hC₁, hC₂, hC₃]
  have hc₁ : C₁ ≤ C := by dsimp only [C]; linarith only [hC₀, hC₂, hC₃]
  have hc₂ : C₂ ≤ C := by dsimp only [C]; linarith only [hC₀, hC₁, hC₃]
  have hc₃ : C₃ ≤ C := by dsimp only [C]; linarith only [hC₀, hC₁, hC₂]
  refine ⟨C, hC, fun j f₁ f₂ f₃ hf₁ hf₂ hf₃ hL₁ hL₂ hL₃ => ?_⟩
  have hmono (c : ℝ) (hc : c ≤ C) :
      c * weightedL2Norm s f₁ * weightedL2Norm s f₂ * weightedL2Norm s f₃ ≤
        C * weightedL2Norm s f₁ * weightedL2Norm s f₂ * weightedL2Norm s f₃ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (weightedL2Norm_nonneg _ _))
        (weightedL2Norm_nonneg _ _)) (weightedL2Norm_nonneg _ _)
  fin_cases j
  · obtain ⟨hi, hn⟩ := h₀ f₁ f₂ f₃ hf₁ hf₂ hf₃ hL₁ hL₂ hL₃
    exact ⟨hi, hn.trans (hmono C₀ hc₀)⟩
  · obtain ⟨hi, hn⟩ := h₁ f₁ f₂ f₃ hf₁ hf₂ hf₃ hL₁ hL₂ hL₃
    exact ⟨hi, hn.trans (hmono C₁ hc₁)⟩
  · obtain ⟨hi, hn⟩ := h₂ f₁ f₂ f₃ hf₁ hf₂ hf₃ hL₁ hL₂ hL₃
    exact ⟨hi, hn.trans (hmono C₂ hc₂)⟩
  · obtain ⟨hi, hn⟩ := h₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ hL₁ hL₂ hL₃
    exact ⟨hi, hn.trans (hmono C₃ hc₃)⟩

end WaveTurbulence.WKEL2
