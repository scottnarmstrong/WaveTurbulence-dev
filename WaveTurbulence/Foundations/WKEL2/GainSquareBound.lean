/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.GainAbs
public import WaveTurbulence.Foundations.WKEL2.NonnegativeL2Duality

/-!
# Squared integrability of the weighted absolute gain output

Research-note Proposition 7, with finiteness derived from genuine L² tests.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The weighted absolute gain output has a uniformly bounded squared integral. -/
theorem exists_weighted_absoluteGain_square_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : Mom d, ‖e‖ = 1 → ∀ f₁ f₂ f₃ : Mom d → ℝ,
      Measurable f₁ → Measurable f₂ → Measurable f₃ →
      MemLp (weightedFunction s f₁) 2 → MemLp (weightedFunction s f₂) 2 →
      MemLp (weightedFunction s f₃) 2 →
      (∫⁻ k : Mom d, (ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2)) * absoluteGain e f₁ f₂ f₃ k) ^ 2) ≤
        ENNReal.ofReal ((C * (weightedL2Norm s f₁ * weightedL2Norm s f₂ * weightedL2Norm s f₃)) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_weighted_gain_pairing_bound hd s hs
  refine ⟨C, hC, fun e he f₁ f₂ f₃ h₁ h₂ h₃ hL₁ hL₂ hL₃ => ?_⟩
  have hN : 0 ≤ weightedL2Norm s f₁ * weightedL2Norm s f₂ * weightedL2Norm s f₃ :=
    mul_nonneg (mul_nonneg (weightedL2Norm_nonneg _ _) (weightedL2Norm_nonneg _ _))
      (weightedL2Norm_nonneg _ _)
  have hG : Measurable (fun k : Mom d => ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2)) *
      absoluteGain e f₁ f₂ f₃ k) := (measurable_frozenWeight (d := d) s).mul
    (measurable_absoluteGain e (by omega) h₁ h₂ h₃)
  apply lintegral_sq_le_of_l2_tests hG _ (mul_nonneg hC hN)
  intro F hF hLF
  rw [lintegral_weighted_absoluteGain_test s e (by omega) h₁ h₂ h₃ hF]
  simpa only [ENNReal.ofReal_mul hC] using hb e he f₁ f₂ f₃ F h₁ h₂ h₃ hF hL₁ hL₂ hL₃ hLF

end WaveTurbulence.WKEL2
