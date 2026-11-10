/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.ThreeTimeMoments
public import WaveTurbulence.Foundations.Fourier.JointFrequencyEnvelope
public import WaveTurbulence.Foundations.Fourier.MixedNormBounds
import Mathlib.Tactic

/-!
# Closing the quarter-order mixed norm from eight directional moments

The momentum supremum remains inside the frequency integral. A common
integrable envelope therefore gives a uniform bound even for arbitrary
momentum-dependent phases, without momentum continuity assumptions.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- An absolute finite positive constant for the joint frequency integration. -/
@[expose] noncomputable def jointFrequencyConstant : ℝ :=
  1 + ∫ ξ : Fin 2 → ℝ, jointFrequencyEnvelope (ξ 0, ξ 1)

/-- The actual derivative-moment sum is nonnegative. -/
theorem threeTimeMomentSum_nonneg (f : (Fin 2 → ℝ) → ℂ) : 0 ≤ threeTimeMomentSum f := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
  exact integral_nonneg (fun _ => norm_nonneg _)

/-- Weighted pointwise Fourier control by the common integrable envelope. -/
theorem timeWeight_mul_enorm_timeFourier_le_three_moments {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (ξ : Fin 2 → ℝ) :
    timeWeight (1 / 4) ξ * ‖timeFourier f ξ‖ₑ ≤
      ENNReal.ofReal (8 * jointFrequencyEnvelope (ξ 0, ξ 1)) * ENNReal.ofReal (threeTimeMomentSum f) := by
  have hs := threeTimeMomentSum_nonneg f
  have hw : 0 ≤ timeBracket ξ ^ (1 / 4 : ℝ) := Real.rpow_nonneg (timeBracket_pos ξ).le _
  have hreal : timeBracket ξ ^ (1 / 4 : ℝ) * ‖timeFourier f ξ‖ ≤
      8 * jointFrequencyEnvelope (ξ 0, ξ 1) * threeTimeMomentSum f := by
    calc
      _ ≤ timeBracket ξ ^ (1 / 4 : ℝ) *
          (8 * threeTimeMomentSum f /
            (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2) *
              Real.sqrt (1 + (ξ 0 + ξ 1) ^ 2))) :=
        mul_le_mul_of_nonneg_left (norm_timeFourier_le_three_brackets hf hc ξ) hw
      _ = (8 * threeTimeMomentSum f) *
          (timeBracket ξ ^ (1 / 4 : ℝ) /
            (Real.sqrt (1 + (ξ 0) ^ 2) * Real.sqrt (1 + (ξ 1) ^ 2) *
              Real.sqrt (1 + (ξ 0 + ξ 1) ^ 2))) := by ring
      _ ≤ (8 * threeTimeMomentSum f) * jointFrequencyEnvelope (ξ 0, ξ 1) :=
        mul_le_mul_of_nonneg_left (quarter_weight_three_brackets_le_envelope ξ) (by positivity)
      _ = _ := by ring
  change ENNReal.ofReal (timeBracket ξ ^ (1 / 4 : ℝ)) * ‖timeFourier f ξ‖ₑ ≤ _
  calc
    _ = ENNReal.ofReal (timeBracket ξ ^ (1 / 4 : ℝ) * ‖timeFourier f ξ‖) := by
      rw [ENNReal.ofReal_mul hw, ofReal_norm]
    _ ≤ ENNReal.ofReal (8 * jointFrequencyEnvelope (ξ 0, ξ 1) * threeTimeMomentSum f) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := ENNReal.ofReal_mul (mul_nonneg (by norm_num) (jointFrequencyEnvelope_nonneg _))

end WaveTurbulence.Fourier
