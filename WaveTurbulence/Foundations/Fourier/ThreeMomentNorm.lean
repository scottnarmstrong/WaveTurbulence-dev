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

/-- The frequency constant is at least one. -/
theorem one_le_jointFrequencyConstant : 1 ≤ jointFrequencyConstant := by
  have h : 0 ≤ ∫ ξ : Fin 2 → ℝ, jointFrequencyEnvelope (ξ 0, ξ 1) :=
    integral_nonneg (fun _ => jointFrequencyEnvelope_nonneg _)
  dsimp [jointFrequencyConstant]
  linarith

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

/-- The quarter-order mixed norm is controlled by the uniform eight-moment sum.
The time slices alone are assumed smooth and compactly supported. -/
theorem mixedFourierNorm_quarter_le_three_moments {d : ℕ}
    {F : (Fin 2 → ℝ) → Mom d → ℂ}
    (hF : ∀ k, ContDiff ℝ ∞ (fun t => F t k))
    (hc : ∀ k, HasCompactSupport (fun t => F t k)) :
    mixedFourierNorm (1 / 4) 0 0 F ≤ ENNReal.ofReal (8 * jointFrequencyConstant) *
      ⨆ k, ENNReal.ofReal (threeTimeMomentSum (fun t => F t k)) := by
  let M := ⨆ k, ENNReal.ofReal (threeTimeMomentSum (fun t => F t k))
  let B := fun ξ : Fin 2 → ℝ => ENNReal.ofReal (8 * jointFrequencyEnvelope (ξ 0, ξ 1))
  have hB : Measurable B := by
    exact (measurable_const.mul (jointFrequencyEnvelope_measurable.comp
      (by fun_prop))).ennreal_ofReal
  have hpoint (ξ : Fin 2 → ℝ) (k : Mom d) :
      timeWeight (1 / 4) ξ * ‖mixedTimeFourier F ξ k‖ₑ ≤ B ξ * M :=
    (timeWeight_mul_enorm_timeFourier_le_three_moments (hF k) (hc k) ξ).trans
      (mul_le_mul_right (le_iSup (fun k => ENNReal.ofReal (threeTimeMomentSum (fun t => F t k))) k) _)
  have hnorm := mixedFourierNorm_zero_le_weighted_majorant (1 / 4)
    (fun k => (hF k).continuous.integrable_of_hasCompactSupport (hc k)) hB M hpoint
  apply hnorm.trans
  apply mul_le_mul_left
  have hi := jointFrequencyEnvelope_coordinates_integrable.const_mul (8 : ℝ)
  have hn : 0 ≤ᵐ[volume] (fun ξ : Fin 2 → ℝ => 8 * jointFrequencyEnvelope (ξ 0, ξ 1)) :=
    ae_of_all _ fun _ => mul_nonneg (by norm_num) (jointFrequencyEnvelope_nonneg _)
  rw [show (∫⁻ ξ, B ξ) = ENNReal.ofReal (∫ ξ : Fin 2 → ℝ,
    8 * jointFrequencyEnvelope (ξ 0, ξ 1)) from (ofReal_integral_eq_lintegral_ofReal hi hn).symm]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul]
  dsimp [jointFrequencyConstant]
  linarith

end WaveTurbulence.Fourier
