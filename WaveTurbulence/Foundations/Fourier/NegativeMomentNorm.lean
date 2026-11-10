/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourMomentDecay
public import WaveTurbulence.Foundations.Fourier.NegativeFrequencyEnvelope
public import WaveTurbulence.Foundations.Fourier.MixedNormBounds
import Mathlib.Tactic

/-!
# Negative mixed norms from the four endpoint moments

The momentum supremum remains inside the Fourier integral. No momentum
regularity is required at derivative order zero, by the owner's ruling.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- A finite frequency integration constant for each positive `η`. -/
@[expose] noncomputable def negativeFrequencyConstant (η : ℝ) : ℝ :=
  1 + ∫ ξ, negativeFrequencyEnvelope η ξ

/-- Weighted pointwise Fourier control by the endpoint moments. -/
theorem timeWeight_mul_enorm_timeFourier_le_four_moments {η : ℝ} (hη : 0 ≤ η)
    {f : (Fin 2 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (ξ : Fin 2 → ℝ) :
    timeWeight (-η) ξ * ‖timeFourier f ξ‖ₑ ≤
      ENNReal.ofReal (4 * negativeFrequencyEnvelope η ξ) * fourTimeMomentNorm f := by
  have hs : 0 ≤ fourTimeMomentSum f := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hw := Real.rpow_nonneg (timeBracket_pos ξ).le (-η)
  have hr : timeBracket ξ ^ (-η) * ‖timeFourier f ξ‖ ≤
      (4 * negativeFrequencyEnvelope η ξ) * fourTimeMomentSum f := by
    calc
      _ ≤ timeBracket ξ ^ (-η) * (4 * fourTimeMomentSum f /
        (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2))) :=
          mul_le_mul_of_nonneg_left (norm_timeFourier_le_two_brackets hf hc ξ) hw
      _ = (4 * fourTimeMomentSum f) * (timeBracket ξ ^ (-η) /
        (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2))) := by ring
      _ ≤ (4 * fourTimeMomentSum f) * negativeFrequencyEnvelope η ξ :=
        mul_le_mul_of_nonneg_left (negative_weight_two_brackets_le hη ξ) (by positivity)
      _ = _ := by ring
  rw [← ofReal_fourTimeMomentSum hf hc]
  change ENNReal.ofReal (timeBracket ξ ^ (-η)) * ‖timeFourier f ξ‖ₑ ≤ _
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hw,
    ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (negativeFrequencyEnvelope_nonneg η ξ))]
  exact ENNReal.ofReal_le_ofReal hr

end WaveTurbulence.Fourier
