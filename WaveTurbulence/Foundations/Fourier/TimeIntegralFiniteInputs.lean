/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.KernelSmoothExtension
public import WaveTurbulence.Foundations.Fourier.RectangleTimeIntegralBounds
public import WaveTurbulence.Foundations.Fourier.TriangleTimeIntegralBounds
import Mathlib.Tactic

/-!
# TARGET A.2 on arbitrary finite-norm inputs

Smooth compact approximation is applied only after proving the literal
kernel identities and physical L1 continuity. Momentum slices in the
triangular estimate need no regularity in momentum.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- The rectangular A.2 bound on arbitrary finite `L^{1+3η}` inputs. -/
theorem timeFourierNorm_cutoffDoubleIntegral_memLp_le {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 3) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h : CutoffControl χ) {F : (Fin 2 → ℝ) → ℂ}
    (hF : MemLp F (ENNReal.ofReal (1 + 3 * η))) :
    timeFourierNorm η (cutoffDoubleIntegral χ F) ≤
      rectangleTimeFactor η h.radius h.bound * eLpNorm F (ENNReal.ofReal (1 + 3 * η)) := by
  have hp : 1 ≤ 1 + 3 * η := by linarith
  rw [cutoffDoubleIntegral_eq_kernel (triangleAmplitude_integrable_of_memLp hp hχ h hF)]
  apply timeFourierNorm_localizedKernel_le_of_smooth_bound hp hχ h
    rectangleTimeKernel_measurable norm_rectangleTimeKernel_le η
    (rectangleTimeFactor_ne_top hη hη1 _ _) _ hF
  intro g hgs hgc
  rw [← cutoffDoubleIntegral_eq_kernel (triangleAmplitude_integrable_of_memLp hp hχ h
    (hgs.continuous.memLp_of_hasCompactSupport hgc))]
  exact timeFourierNorm_cutoffDoubleIntegral_smooth_le hη hη1 hχ h hgs

/-- The triangle's weighted pointwise Fourier estimate extends to all integrable inputs. -/
theorem timeWeight_mul_enorm_fourier_triangle_memLp_le {η : ℝ} (hη : 0 < η)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (h : CutoffControl χ)
    {F : (Fin 2 → ℝ) → ℂ} (hF : MemLp F 1) (ξ : Fin 2 → ℝ) :
    timeWeight (-η) ξ * ‖timeFourier (cutoffTriangleIntegral χ F) ξ‖ₑ ≤
      (ENNReal.ofReal (4 * negativeFrequencyEnvelope η ξ) *
        orderedFourMomentFactor h.radius h.bound * ENNReal.ofReal (h.bound ^ 2)) * eLpNorm F 1 := by
  have hFp : MemLp F (ENNReal.ofReal (1 : ℝ)) := by simpa using hF
  rw [cutoffTriangleIntegral_eq_kernel (triangleAmplitude_integrable_of_memLp (by norm_num) hχ h hFp)]
  have hconst : ENNReal.ofReal (4 * negativeFrequencyEnvelope η ξ) *
      orderedFourMomentFactor h.radius h.bound * ENNReal.ofReal (h.bound ^ 2) ≠ ⊤ := by
    have hm := orderedFourMomentFactor_ne_top h.radius h.bound
    finiteness
  have hh := weighted_fourier_localizedKernel_le_of_smooth_bound (p := 1) (by norm_num) hχ h
    triangleTimeKernel_measurable norm_triangleTimeKernel_le ξ
    (show timeWeight (-η) ξ ≠ ⊤ from ENNReal.ofReal_ne_top) hconst
    (fun g hgs hgc => ?_) hFp
  simpa only [ENNReal.ofReal_one] using hh
  rw [← cutoffTriangleIntegral_eq_kernel (triangleAmplitude_integrable_of_memLp (p := 1)
    (by norm_num) hχ h (hgs.continuous.memLp_of_hasCompactSupport hgc))]
  apply (timeWeight_mul_enorm_timeFourier_le_four_moments hη.le
    (cutoffTriangleIntegral_contDiff hχ hgs)
    (cutoffTriangleIntegral_hasCompactSupport hcχ g) ξ).trans
  exact (mul_le_mul_right (fourTimeMomentNorm_triangle_le hχ h hgs) _).trans_eq (by
    rw [ENNReal.ofReal_one]
    ring)

/-- The triangular A.2 bound on arbitrary integrable slices, with the supremum inside the Fourier integral. -/
theorem mixedFourierNorm_cutoffJ_memLp_le {η : ℝ} (hη : 0 < η) {d : ℕ}
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (h : CutoffControl χ) {F : (Fin 2 → ℝ) → Mom d → ℂ}
    (hF : ∀ k, MemLp (fun t => F t k) 1) :
    mixedFourierNorm (-η) 0 0 (cutoffJ χ F) ≤
      (ENNReal.ofReal (4 * negativeFrequencyConstant η) *
        orderedFourMomentFactor h.radius h.bound * ENNReal.ofReal (h.bound ^ 2)) * uniformTimeL1 F := by
  let M := (orderedFourMomentFactor h.radius h.bound * ENNReal.ofReal (h.bound ^ 2)) * uniformTimeL1 F
  let B := fun ξ => ENNReal.ofReal (4 * negativeFrequencyEnvelope η ξ)
  have hB : Measurable B := by
    dsimp [B]
    unfold negativeFrequencyEnvelope inverseBracketPower
    fun_prop
  have hfi (k : Mom d) : Integrable (fun t => cutoffJ χ F t k) := by
    change Integrable (cutoffTriangleIntegral χ (fun t => F t k))
    rw [cutoffTriangleIntegral_eq_kernel (triangleAmplitude_integrable_of_memLp (p := 1)
      (by norm_num) hχ h (by simpa using hF k))]
    exact localizedKernelOperator_integrable (p := 1) (by norm_num) hχ h
      triangleTimeKernel_measurable norm_triangleTimeKernel_le (by simpa using hF k)
  have hp (ξ : Fin 2 → ℝ) (k : Mom d) :
      timeWeight (-η) ξ * ‖mixedTimeFourier (cutoffJ χ F) ξ k‖ₑ ≤ B ξ * M := by
    apply (timeWeight_mul_enorm_fourier_triangle_memLp_le hη hχ hcχ h (hF k) ξ).trans
    have hs : eLpNorm (fun t => F t k) 1 ≤ uniformTimeL1 F :=
      le_iSup (fun k => eLpNorm (fun t => F t k) 1) k
    have hh := mul_le_mul_right hs (ENNReal.ofReal (4 * negativeFrequencyEnvelope η ξ) *
      orderedFourMomentFactor h.radius h.bound * ENNReal.ofReal (h.bound ^ 2))
    exact hh.trans_eq (by dsimp [B, M]; ring)
  apply (mixedFourierNorm_zero_le_weighted_majorant (-η) hfi hB M hp).trans
  have hi := (negativeFrequencyEnvelope_integrable hη).const_mul (4 : ℝ)
  have hn : 0 ≤ᵐ[volume] (fun ξ => 4 * negativeFrequencyEnvelope η ξ) :=
    ae_of_all _ fun ξ => mul_nonneg (by norm_num) (negativeFrequencyEnvelope_nonneg η ξ)
  have hbi : (∫⁻ ξ, B ξ) ≤ ENNReal.ofReal (4 * negativeFrequencyConstant η) := by
    rw [show (∫⁻ ξ, B ξ) = ENNReal.ofReal (∫ ξ, 4 * negativeFrequencyEnvelope η ξ) from
      (ofReal_integral_eq_lintegral_ofReal hi hn).symm]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_const_mul]
    dsimp [negativeFrequencyConstant]
    linarith
  exact (mul_le_mul_left hbi M).trans_eq (by dsimp [M]; ring)

end WaveTurbulence.Fourier
