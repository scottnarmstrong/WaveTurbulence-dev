/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeIntegralFiniteInputs
public import WaveTurbulence.Foundations.Fourier.Norm00V

/-!
# The landed triangular negative estimate on arbitrary parameter carriers

Only the parameter type is generalized. The scalar pointwise Fourier
estimate and its integrable envelope are reused without modification.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh
open _root_.WaveTurbulence.Fourier

/-- The literal triangular cutoff operator is integrable on every physical L¹ input. -/
theorem integrable_cutoffTriangleIntegral {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) {F : (Fin 2 → ℝ) → ℂ} (hF : Integrable F) :
    Integrable (cutoffTriangleIntegral χ F) := by
  have hm : MemLp F (ENNReal.ofReal (1 : ℝ)) := by
    simpa only [ENNReal.ofReal_one] using memLp_one_iff_integrable.mpr hF
  have ha := triangleAmplitude_integrable_of_memLp (le_refl (1 : ℝ)) hχ h hm
  rw [cutoffTriangleIntegral_eq_kernel ha]
  exact cutoffKernelIntegral_integrable hχ.continuous h triangleTimeKernel_measurable
    norm_triangleTimeKernel_le ha

/-- TARGET (incohproof26) on any parameter carrier, from the landed scalar N3 estimate. -/
theorem mixedFourierNorm00_cutoffTriangle_le {V : Type*} {η : ℝ} (hη : 0 < η)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (h : CutoffControl χ)
    (F : (Fin 2 → ℝ) → V → ℂ) (hF : ∀ v, Integrable (fun t => F t v))
    {M : ℝ≥0∞} (hM : ∀ v, eLpNorm (fun t => F t v) 1 ≤ M) :
    mixedFourierNorm00 (-η) (fun t v => cutoffTriangleIntegral χ (fun u => F u v) t) ≤
      (ENNReal.ofReal (4 * negativeFrequencyConstant η) *
        orderedFourMomentFactor h.radius h.bound * ENNReal.ofReal (h.bound ^ 2)) * M := by
  let B := fun ξ : Fin 2 → ℝ => ENNReal.ofReal (4 * negativeFrequencyEnvelope η ξ)
  let A := orderedFourMomentFactor h.radius h.bound * ENNReal.ofReal (h.bound ^ 2)
  have hB : Measurable B := by
    unfold B negativeFrequencyEnvelope inverseBracketPower
    fun_prop
  have hi (v : V) := integrable_cutoffTriangleIntegral hχ h (hF v)
  have hp (ξ : Fin 2 → ℝ) : timeWeight (-η) ξ *
      mixedFourierEnvelope00 (fun t v => cutoffTriangleIntegral χ (fun u => F u v) t) ξ ≤ B ξ * (A * M) := by
    unfold mixedFourierEnvelope00
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro v
    exact (timeWeight_mul_enorm_fourier_triangle_memLp_le hη hχ hcχ h
      (memLp_one_iff_integrable.mpr (hF v)) ξ).trans
      ((mul_le_mul' le_rfl (hM v)).trans_eq (by dsimp only [B, A]; ring))
  have hInt : (∫⁻ ξ, B ξ) ≤ ENNReal.ofReal (4 * negativeFrequencyConstant η) := by
    have hiB := (negativeFrequencyEnvelope_integrable hη).const_mul (4 : ℝ)
    have hn : 0 ≤ᵐ[volume] (fun ξ => 4 * negativeFrequencyEnvelope η ξ) :=
      ae_of_all _ (fun ξ => mul_nonneg (by norm_num) (negativeFrequencyEnvelope_nonneg η ξ))
    rw [show (∫⁻ ξ, B ξ) = ENNReal.ofReal (∫ ξ, 4 * negativeFrequencyEnvelope η ξ) from
      (ofReal_integral_eq_lintegral_ofReal hiB hn).symm]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_const_mul]
    dsimp only [negativeFrequencyConstant]
    linarith
  rw [mixedFourierNorm00_eq_lintegral hi]
  exact (lintegral_mono hp).trans ((lintegral_mul_const (A * M) hB).le.trans
    ((mul_le_mul' hInt le_rfl).trans_eq (by dsimp only [A]; ring)))

end WaveTurbulence.Incoh
