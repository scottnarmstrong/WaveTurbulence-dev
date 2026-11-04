/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CutoffDoubleL1

/-!
# Pointwise physical control of the actual cutoff operators

The landed bounded kernels give a uniform pointwise bound on every
integrable input, useful for exact pointwise spectral recombination.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh
open _root_.WaveTurbulence.Fourier

/-- A unit-bounded literal time kernel gives a pointwise L¹ input estimate. -/
theorem enorm_localizedKernelOperator_le {χ : ℝ → ℝ} (_hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ}
    (hK : ∀ t v, ‖K t v‖ ≤ 1) {F : (Fin 2 → ℝ) → ℂ} (hF : Integrable F)
    (t : Fin 2 → ℝ) :
    ‖localizedKernelOperator χ K F t‖ₑ ≤ ENNReal.ofReal h.bound ^ 4 * eLpNorm F 1 := by
  have hb (s : ℝ) : ‖(χ s : ℂ)‖ₑ ≤ ENNReal.ofReal h.bound := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (h.abs_le s)
  have hi : (∫⁻ v, ‖K t v * triangleAmplitude χ F v‖ₑ) ≤
      ENNReal.ofReal h.bound ^ 2 * eLpNorm F 1 := by
    rw [eLpNorm_one_eq_lintegral_enorm hF.aestronglyMeasurable]
    apply (lintegral_mono (fun v => ?_)).trans_eq
      (lintegral_const_mul'' _ hF.aestronglyMeasurable.enorm)
    have hk : ‖K t v‖ₑ ≤ 1 := by
      rw [← ofReal_norm]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hK t v)
    simp only [triangleAmplitude, coordinateCutoff, Fin.prod_univ_two]
    change ‖K t v * ((χ (v 0) : ℂ) * (χ (v 1) : ℂ) * F v)‖ₑ ≤ _
    simp only [enorm_mul]
    exact (mul_le_mul' hk (mul_le_mul' (mul_le_mul' (hb _) (hb _)) le_rfl)).trans_eq
      (by ring)
  unfold localizedKernelOperator cutoffKernelIntegral
  rw [enorm_mul, enorm_mul]
  calc
    _ ≤ (ENNReal.ofReal h.bound * ENNReal.ofReal h.bound) *
        ∫⁻ v, ‖K t v * triangleAmplitude χ F v‖ₑ :=
      mul_le_mul' (mul_le_mul' (hb _) (hb _)) (enorm_integral_le_lintegral_enorm _)
    _ ≤ _ := (mul_le_mul' le_rfl hi).trans_eq (by ring)

/-- Pointwise rectangular cutoff bound for every actual integrable input. -/
theorem enorm_cutoffDoubleIntegral_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) {F : (Fin 2 → ℝ) → ℂ} (hF : Integrable F) (t : Fin 2 → ℝ) :
    ‖cutoffDoubleIntegral χ F t‖ₑ ≤ ENNReal.ofReal h.bound ^ 4 * eLpNorm F 1 := by
  have hm : MemLp F (ENNReal.ofReal (1 : ℝ)) := by
    simpa only [ENNReal.ofReal_one] using memLp_one_iff_integrable.mpr hF
  have ha := triangleAmplitude_integrable_of_memLp (le_refl (1 : ℝ)) hχ h hm
  rw [cutoffDoubleIntegral_eq_kernel ha]
  exact enorm_localizedKernelOperator_le hχ h norm_rectangleTimeKernel_le hF t

/-- Pointwise triangular cutoff bound for every actual integrable input. -/
theorem enorm_cutoffTriangleIntegral_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) {F : (Fin 2 → ℝ) → ℂ} (hF : Integrable F) (t : Fin 2 → ℝ) :
    ‖cutoffTriangleIntegral χ F t‖ₑ ≤ ENNReal.ofReal h.bound ^ 4 * eLpNorm F 1 := by
  have hm : MemLp F (ENNReal.ofReal (1 : ℝ)) := by
    simpa only [ENNReal.ofReal_one] using memLp_one_iff_integrable.mpr hF
  have ha := triangleAmplitude_integrable_of_memLp (le_refl (1 : ℝ)) hχ h hm
  rw [cutoffTriangleIntegral_eq_kernel ha]
  exact enorm_localizedKernelOperator_le hχ h norm_triangleTimeKernel_le hF t

end WaveTurbulence.Incoh
