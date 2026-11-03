/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BalancedAmplitude
public import WaveTurbulence.Foundations.Fourier.WeightedOrderedIntegral
import Mathlib.Tactic

/-!
# Literal A.3 operators as balanced-amplitude ordered integrals

These are exact identities, including the oriented signs for reversed
endpoints. No condition is imposed on the momentum phase functions.
-/

public section

namespace WaveTurbulence.Fourier

/-- Exact balanced-amplitude representation of the triangular phase operator. -/
theorem cutoffU_eq_balanced {d : ℕ} (χ : ℝ → ℝ) (Γ : Mom d → ℝ)
    (F : (Fin 2 → ℝ) → Mom d → ℂ) (k : Mom d) :
    (fun t => cutoffU χ Γ F t k) = weightedOrderedIntegral 2 χ χ
      (balancedCutoffAmplitude χ ![Γ k, -Γ k] (fun u => F u k) 0 1) := by
  change cutoffTriangleIntegral χ
    (fun u => Complex.exp ((Γ k * (u 0 - u 1) : ℝ) * Complex.I) * F u k) = _
  rw [cutoffTriangleIntegral_eq_ordered, ← weightedOrderedIntegral_self]
  congr 1
  funext v
  have he : ![v 0, v 1] = v := by ext j; fin_cases j <;> rfl
  simp only [triangleAmplitude, balancedCutoffAmplitude, linearTimePhase_two, he]
  ring

/-- Exact balanced-amplitude representation of the fourfold phase operator. -/
theorem cutoffV_eq_balanced {d : ℕ} (χ : ℝ → ℝ) (Γ₁ Γ₂ : Mom d → ℝ)
    (F : (Fin 2 → ℝ) → Mom d → ℂ) (k : Mom d) :
    (fun t => cutoffV χ Γ₁ Γ₂ F t k) = weightedOrderedIntegral 4 χ χ
      (balancedCutoffAmplitude χ ![Γ₁ k, -Γ₁ k, Γ₂ k, -Γ₂ k] (fun u => F u k) 1 2) := by
  rw [cutoffV_eq_ordered, ← weightedOrderedIntegral_self]
  congr 1
  funext v
  simp only [fourfoldAmplitude, balancedCutoffAmplitude, linearTimePhase_four]
  ring

end WaveTurbulence.Fourier
