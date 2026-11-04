/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.PositiveMomentNorm
public import WaveTurbulence.Foundations.Fourier.CoordinateCutoffDerivative
import Mathlib.Tactic

/-!
# TARGET A.2: the rectangular bound on smooth inputs

The source exponent is exactly `1 + 3η`; `0 < η ≤ 1/3` is an explicit
small-parameter range. The proof uses physical endpoint moments and
Hausdorff–Young, repairing the missing logarithm at TARGET L2370.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- An explicit extended-valued expression for the rectangular operator constant. -/
@[expose] noncomputable def rectangleTimeFactor (η R C : ℝ) : ℝ≥0∞ :=
  (4 * positiveFrequencyFactor η (1 + 3 * η)) *
    rectangleFourLpFactor (1 + 3 * η) R C * ENNReal.ofReal (C ^ 2)

/-- The rectangular operator factor is finite on the stated small-parameter range. -/
theorem rectangleTimeFactor_ne_top {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 3)
    (R C : ℝ) : rectangleTimeFactor η R C ≠ ⊤ := by
  have hp : 1 < 1 + 3 * η := by linarith
  have hm : 1 < (1 - η) * (1 + 3 * η) := by nlinarith
  have hf := positiveFrequencyFactor_ne_top (by linarith : 0 < 1 + 3 * η) hm
  have hg := rectangleFourLpFactor_ne_top hp R C
  unfold rectangleTimeFactor
  finiteness

/-- The two input cutoffs preserve every `Lᵖ` norm with their squared uniform bound. -/
theorem eLpNorm_triangleAmplitude_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) {F : (Fin 2 → ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) (p : ℝ≥0∞) :
    eLpNorm (triangleAmplitude χ F) p ≤ ENNReal.ofReal (h.bound ^ 2) * eLpNorm F p := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (triangleAmplitude_contDiff hχ hF).continuous.aestronglyMeasurable
  exact ae_of_all _ fun t => by
    rw [triangleAmplitude, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_coordinateCutoff_le h t) (norm_nonneg _)

/-- TARGET A.2's rectangular estimate for smooth inputs, without an input support restriction. -/
theorem timeFourierNorm_cutoffDoubleIntegral_smooth_le {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 3) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) {F : (Fin 2 → ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) :
    timeFourierNorm η (cutoffDoubleIntegral χ F) ≤
      rectangleTimeFactor η h.radius h.bound * eLpNorm F (ENNReal.ofReal (1 + 3 * η)) := by
  have hp : 1 < 1 + 3 * η := by linarith
  have hp2 : 1 + 3 * η ≤ 2 := by linarith
  have hpq := Real.HolderConjugate.conjExponent hp
  have hR : 0 ≤ h.radius := le_trans (by norm_num) h.one_le_radius
  have hC : 0 ≤ h.bound := le_trans (by norm_num) h.one_le_bound
  have hA := triangleAmplitude_contDiff hχ hF
  rw [cutoffDoubleIntegral_eq_weightedRectangle]
  apply (timeFourierNorm_positive_le_four_Lp hη.le hpq hp2
    (weightedRectangle_contDiff hχ hχ hA)
    (weightedRectangle_hasCompactSupport h.endpointBounds h.endpointBounds _)).trans
  have hm := fourTimeLpNorm_weightedRectangle_le hp hR hC hχ hχ
    h.endpointBounds h.deriv_endpointBounds h.endpointBounds h.deriv_endpointBounds hA
  apply (mul_le_mul_right hm _).trans
  exact (mul_le_mul_right (mul_le_mul_right (eLpNorm_triangleAmplitude_le hχ h hF _) _) _).trans_eq
    (by unfold rectangleTimeFactor; ring)

end WaveTurbulence.Fourier
