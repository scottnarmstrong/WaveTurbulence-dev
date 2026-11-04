/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.LocalizedKernelOperator

/-!
# Physical L¹ control of the literal triangular cutoff extension

This reuses the landed bounded-kernel and localized-input estimates at
physical exponent one, and is used only to justify spectral Fubini.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh
open _root_.WaveTurbulence.Fourier

/-- The exact triangular cutoff operator has a fixed finite physical L¹ cost. -/
theorem eLpNorm_cutoffTriangleIntegral_one_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) {F : (Fin 2 → ℝ) → ℂ} (hF : Integrable F) :
    eLpNorm (cutoffTriangleIntegral χ F) 1 ≤
      (cutoffKernelL1Factor h.radius h.bound * localTimeL1Factor 1 h.radius h.bound) *
        eLpNorm F 1 := by
  have hm : MemLp F (ENNReal.ofReal (1 : ℝ)) := by simpa only [ENNReal.ofReal_one] using (memLp_one_iff_integrable.mpr hF)
  have ha := triangleAmplitude_integrable_of_memLp (le_refl (1 : ℝ)) hχ h hm
  rw [cutoffTriangleIntegral_eq_kernel ha]
  apply (eLpNorm_cutoffKernelIntegral_one_le hχ.continuous h triangleTimeKernel_measurable
    norm_triangleTimeKernel_le ha).trans
  apply (mul_le_mul' le_rfl (eLpNorm_triangleAmplitude_one_le (le_refl (1 : ℝ)) hχ h
    hF.aestronglyMeasurable)).trans_eq
  simp only [ENNReal.ofReal_one, mul_assoc]

end WaveTurbulence.Incoh
