/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.Trilinear
public import WaveTurbulence.Foundations.WKEL2.CollisionDecomposition
public import WaveTurbulence.Foundations.WKEL2.WeightedL2Order

/-!
# The full collision operator on the frozen weighted L² domain
-/

public section

noncomputable section

open MeasureTheory

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The full signed collision operator is bounded on the exact weighted L² space. -/
theorem exists_collisionOp_bound (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f₁ f₂ f₃ : Mom d → ℝ,
      Measurable f₁ → Measurable f₂ → Measurable f₃ →
      MemLp (weightedFunction s f₁) 2 → MemLp (weightedFunction s f₂) 2 →
      MemLp (weightedFunction s f₃) 2 →
      MemLp (weightedFunction s (collisionOp f₁ f₂ f₃)) 2 ∧
      weightedL2Norm s (collisionOp f₁ f₂ f₃) ≤
        C * weightedL2Norm s f₁ * weightedL2Norm s f₂ * weightedL2Norm s f₃ := by
  obtain ⟨C, hC, hb⟩ := exists_collisionTerm_bound hd s hs
  refine ⟨4 * C, by positivity, fun f₁ f₂ f₃ h₁ h₂ h₃ hL₁ hL₂ hL₃ => ?_⟩
  let F₀ := collisionTerm 0 f₁ f₂ f₃
  let F₁ := collisionTerm 1 f₁ f₂ f₃
  let F₂ := collisionTerm 2 f₁ f₂ f₃
  let F₃ := collisionTerm 3 f₁ f₂ f₃
  let M := C * weightedL2Norm s f₁ * weightedL2Norm s f₂ * weightedL2Norm s f₃
  obtain ⟨hi₀, hn₀⟩ := hb 0 f₁ f₂ f₃ h₁ h₂ h₃ hL₁ hL₂ hL₃
  obtain ⟨hi₁, hn₁⟩ := hb 1 f₁ f₂ f₃ h₁ h₂ h₃ hL₁ hL₂ hL₃
  obtain ⟨hi₂, hn₂⟩ := hb 2 f₁ f₂ f₃ h₁ h₂ h₃ hL₁ hL₂ hL₃
  obtain ⟨hi₃, hn₃⟩ := hb 3 f₁ f₂ f₃ h₁ h₂ h₃ hL₁ hL₂ hL₃
  have hi₀₁ := memLp_weighted_sub s (f := F₀) (g := F₁) hi₀ hi₁
  have hi₀₁₂ := memLp_weighted_add s (f := F₀ - F₁) (g := F₂) hi₀₁ hi₂
  have hiSum := memLp_weighted_sub s (f := F₀ - F₁ + F₂) (g := F₃) hi₀₁₂ hi₃
  have heq : collisionOp f₁ f₂ f₃ =ᵐ[volume] F₀ - F₁ + F₂ - F₃ := by
    filter_upwards [collisionOp_eq_sum_ae hd s hs h₁ h₂ h₃ hL₁ hL₂ hL₃] with k hk
    simpa only [F₀, F₁, F₂, F₃, Pi.sub_apply, Pi.add_apply] using hk
  refine ⟨memLp_weighted_congr_ae s hiSum heq.symm, ?_⟩
  rw [weightedL2Norm_congr_ae s heq]
  calc
    _ ≤ weightedL2Norm s (F₀ - F₁ + F₂) + weightedL2Norm s F₃ :=
      weightedL2Norm_sub_le s hi₀₁₂ hi₃
    _ ≤ (weightedL2Norm s (F₀ - F₁) + weightedL2Norm s F₂) + weightedL2Norm s F₃ :=
      add_le_add (weightedL2Norm_add_le s hi₀₁ hi₂) le_rfl
    _ ≤ ((weightedL2Norm s F₀ + weightedL2Norm s F₁) + weightedL2Norm s F₂) +
        weightedL2Norm s F₃ :=
      add_le_add (add_le_add (weightedL2Norm_sub_le s hi₀ hi₁) le_rfl) le_rfl
    _ ≤ ((M + M) + M) + M := add_le_add (add_le_add (add_le_add hn₀ hn₁) hn₂) hn₃
    _ = _ := by dsimp only [M]; ring

end WaveTurbulence.WKEL2
