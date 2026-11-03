/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.CutoffEightMoments
public import WaveTurbulence.Foundations.Fourier.PhaseAmplitudeBounds
public import WaveTurbulence.Foundations.Fourier.TimeOperatorBalanced
import Mathlib.Tactic

/-!
# The eight actual moments of the literal A.3 operators

Both estimates are uniform in arbitrary momentum phase functions. The
source time slice is smooth and compactly supported, as ruled by the owner.
The support radius of the source never enters the constants.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- The literal triangular phase operator has eight moments controlled by the source mixed derivative. -/
theorem threeTimeMomentSum_cutoffU_le {d : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) (Γ : Mom d → ℝ) (F : (Fin 2 → ℝ) → Mom d → ℂ) (k : Mom d)
    (hF : ContDiff ℝ ∞ (fun t => F t k)) (hc : HasCompactSupport (fun t => F t k)) :
    ENNReal.ofReal (threeTimeMomentSum (fun t => cutoffU χ Γ F t k)) ≤
      orderedFourMomentFactor h.radius h.bound * triangularAmplitudeFactor h.radius h.bound *
        ∫⁻ x, ‖mixedTimePartial (fun t => F t k) x‖ₑ := by
  rw [cutoffU_eq_balanced]
  have hA := balancedCutoffAmplitude_contDiff hχ hF ![Γ k, -Γ k] (0 : Fin 2) 1
  apply (threeTimeMomentSum_weighted_cutoff_le hχ hA h).trans
  exact (mul_le_mul' le_rfl (triangular_amplitude_boxes_le hχ hF hc h (Γ k))).trans_eq (by ring)

/-- The literal fourfold phase operator obeys the same frequency-independent source bound. -/
theorem threeTimeMomentSum_cutoffV_le {d : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) (Γ₁ Γ₂ : Mom d → ℝ) (F : (Fin 2 → ℝ) → Mom d → ℂ) (k : Mom d)
    (hF : ContDiff ℝ ∞ (fun t => F t k)) (hc : HasCompactSupport (fun t => F t k)) :
    ENNReal.ofReal (threeTimeMomentSum (fun t => cutoffV χ Γ₁ Γ₂ F t k)) ≤
      orderedFourMomentFactor h.radius h.bound * fourfoldAmplitudeFactor h.radius h.bound *
        ∫⁻ x, ‖mixedTimePartial (fun t => F t k) x‖ₑ := by
  rw [cutoffV_eq_balanced]
  have hA := balancedCutoffAmplitude_contDiff hχ hF ![Γ₁ k, -Γ₁ k, Γ₂ k, -Γ₂ k] (1 : Fin 4) 2
  apply (threeTimeMomentSum_weighted_cutoff_le hχ hA h).trans
  exact (mul_le_mul' le_rfl (fourfold_amplitude_boxes_le hχ hF hc h (Γ₁ k) (Γ₂ k))).trans_eq (by ring)

end WaveTurbulence.Fourier
