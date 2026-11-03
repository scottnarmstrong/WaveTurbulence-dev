/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.LossOneTrilinear
public import WaveTurbulence.Foundations.WKEL2.ResonantSignedSymmetry

/-!
# The third loss term by resonant symmetry

The j = 3 case of research-note Theorem 7.
-/

public section

noncomputable section

open MeasureTheory

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The third loss term is the first loss term with its outside inputs exchanged. -/
theorem collisionTerm_three_eq_one (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s)
    {e : Mom d} (he : ‖e‖ = 1) {f₁ f₂ : Mom d → ℝ}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂)
    (hL₁ : MemLp (weightedFunction s f₁) 2) (hL₂ : MemLp (weightedFunction s f₂) 2)
    (f₃ : Mom d → ℝ) :
    collisionTerm 3 f₁ f₂ f₃ = collisionTerm 1 f₃ f₂ f₁ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_lossOne_signed hd s hs
  funext k
  let F : Mom d × Mom d → ℝ := fun p => f₃ k * (f₂ (k + p.1 + p.2) * f₁ (k + p.2))
  have hi : Integrable F (resonantMeasure e) :=
    (hb e he f₂ f₁ h₂ h₁ hL₂ hL₁ k).1.const_mul (f₃ k)
  calc
    _ = deltaInt (fun a b => F (b, a)) := by
      apply WKE.deltaInt_congr
      intro a b
      dsimp only [F, collisionKernel]
      rw [show k + b + a = k + a + b by abel]
      ring
    _ = deltaInt (fun a b => F (a, b)) := deltaInt_swap_of_integrable he (by omega) hi
    _ = _ := by
      apply WKE.deltaInt_congr
      intro a b
      dsimp only [F, collisionKernel]
      ring

/-- The signed j = 3 estimate, including genuine weighted-L² membership. -/
theorem exists_collisionTerm_three_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f₁ f₂ f₃ : Mom d → ℝ,
      Measurable f₁ → Measurable f₂ → Measurable f₃ →
      MemLp (weightedFunction s f₁) 2 → MemLp (weightedFunction s f₂) 2 →
      MemLp (weightedFunction s f₃) 2 →
      MemLp (weightedFunction s (collisionTerm 3 f₁ f₂ f₃)) 2 ∧
      weightedL2Norm s (collisionTerm 3 f₁ f₂ f₃) ≤
        C * weightedL2Norm s f₁ * weightedL2Norm s f₂ * weightedL2Norm s f₃ := by
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : Mom d)
  have he : ‖unitVec v‖ = 1 := norm_unitVec hv
  obtain ⟨C, hC, hb⟩ := exists_collisionTerm_one_bound hd s hs
  refine ⟨C, hC, fun f₁ f₂ f₃ h₁ h₂ h₃ hL₁ hL₂ hL₃ => ?_⟩
  rw [collisionTerm_three_eq_one hd s hs he h₁ h₂ hL₁ hL₂ f₃]
  obtain ⟨hi, hnorm⟩ := hb f₃ f₂ f₁ h₃ h₂ h₁ hL₃ hL₂ hL₁
  refine ⟨hi, hnorm.trans_eq ?_⟩
  ring

end WaveTurbulence.WKEL2
