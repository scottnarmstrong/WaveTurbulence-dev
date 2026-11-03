/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.KernelIntegrability

/-!
# The full collision decomposition for weighted L² inputs

The signed resonant-kernel integrability needed for linearity is proved
almost everywhere from the weighted L² estimates.
-/

public section

noncomputable section

open MeasureTheory

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Integral linearity gives the full collision decomposition whenever all four kernels are integrable. -/
theorem collisionOp_eq_sum_of_integrable {e : Mom d} (he : ‖e‖ = 1)
    (f₁ f₂ f₃ : Mom d → ℝ) (k : Mom d)
    (hi : ∀ j : Fin 4, Integrable (fun p : Mom d × Mom d =>
      collisionKernel j f₁ f₂ f₃ k p.1 p.2) (resonantMeasure e)) :
    collisionOp f₁ f₂ f₃ k = collisionTerm 0 f₁ f₂ f₃ k - collisionTerm 1 f₁ f₂ f₃ k +
      collisionTerm 2 f₁ f₂ f₃ k - collisionTerm 3 f₁ f₂ f₃ k := by
  let F (j : Fin 4) (p : Mom d × Mom d) := collisionKernel j f₁ f₂ f₃ k p.1 p.2
  have h₀ : Integrable (F 0) (resonantMeasure e) := hi 0
  have h₁ : Integrable (F 1) (resonantMeasure e) := hi 1
  have h₂ : Integrable (F 2) (resonantMeasure e) := hi 2
  have h₃ : Integrable (F 3) (resonantMeasure e) := hi 3
  let H := F 0 - F 1 + F 2 - F 3
  have hH : Integrable H (resonantMeasure e) := ((h₀.sub h₁).add h₂).sub h₃
  have hInt : (∫ p, H p ∂resonantMeasure e) =
      (∫ p, F 0 p ∂resonantMeasure e) - (∫ p, F 1 p ∂resonantMeasure e) +
        (∫ p, F 2 p ∂resonantMeasure e) - ∫ p, F 3 p ∂resonantMeasure e := by
    have houter := integral_sub ((h₀.sub h₁).add h₂) h₃
    have hmiddle := integral_add (h₀.sub h₁) h₂
    have hinner := integral_sub h₀ h₁
    simp only [Pi.add_apply, Pi.sub_apply] at houter hmiddle hinner
    rw [hmiddle, hinner] at houter
    simpa only [H, Pi.add_apply, Pi.sub_apply] using houter
  rw [integral_resonantMeasure_eq_two_deltaInt he hH,
    integral_resonantMeasure_eq_two_deltaInt he h₀, integral_resonantMeasure_eq_two_deltaInt he h₁,
    integral_resonantMeasure_eq_two_deltaInt he h₂, integral_resonantMeasure_eq_two_deltaInt he h₃] at hInt
  have hK : (fun a b => H (a, b)) = collisionIntegrand f₁ f₂ f₃ k := by
    funext a b
    dsimp only [H, F, Pi.sub_apply, Pi.add_apply]
    exact (collisionIntegrand_eq f₁ f₂ f₃ k a b).symm
  rw [hK, ← collisionOp_eq_deltaInt] at hInt
  change 2 * collisionOp f₁ f₂ f₃ k = 2 * collisionTerm 0 f₁ f₂ f₃ k -
    2 * collisionTerm 1 f₁ f₂ f₃ k + 2 * collisionTerm 2 f₁ f₂ f₃ k -
      2 * collisionTerm 3 f₁ f₂ f₃ k at hInt
  linarith only [hInt]

/-- TARGET's decomposition holds almost everywhere on the full weighted L² domain. -/
theorem collisionOp_eq_sum_ae (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s)
    {f₁ f₂ f₃ : Mom d → ℝ} (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃)
    (hL₁ : MemLp (weightedFunction s f₁) 2) (hL₂ : MemLp (weightedFunction s f₂) 2)
    (hL₃ : MemLp (weightedFunction s f₃) 2) :
    ∀ᵐ k : Mom d, collisionOp f₁ f₂ f₃ k = collisionTerm 0 f₁ f₂ f₃ k - collisionTerm 1 f₁ f₂ f₃ k +
      collisionTerm 2 f₁ f₂ f₃ k - collisionTerm 3 f₁ f₂ f₃ k := by
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : Mom d)
  have he : ‖unitVec v‖ = 1 := norm_unitVec hv
  have hI := ae_integrable_collisionKernel hd s hs he h₁ h₂ h₃ hL₁ hL₂ hL₃
  filter_upwards [hI 0, hI 1, hI 2, hI 3] with k h₀ h₁' h₂' h₃'
  apply collisionOp_eq_sum_of_integrable he f₁ f₂ f₃ k
  intro j
  fin_cases j <;> assumption

end WaveTurbulence.WKEL2
