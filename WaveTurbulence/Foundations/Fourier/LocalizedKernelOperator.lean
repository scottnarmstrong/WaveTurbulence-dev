/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.CutoffKernelIntegral
public import WaveTurbulence.Foundations.Fourier.LocalizedTimeLp
import Mathlib.Tactic

/-!
# Localized bounded kernel operators on finite-norm inputs

The two inner cutoff factors turn physical `Lᵖ` convergence into `L¹`
convergence of amplitudes, and hence into `L¹` convergence of outputs.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- The bounded kernel transform with both input and output cutoff factors. -/
@[expose] noncomputable def localizedKernelOperator (χ : ℝ → ℝ)
    (K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ) (F : (Fin 2 → ℝ) → ℂ) :
    (Fin 2 → ℝ) → ℂ := cutoffKernelIntegral χ K (triangleAmplitude χ F)

/-- Literal kernel identification for the rectangular source operator. -/
theorem cutoffDoubleIntegral_eq_kernel {χ : ℝ → ℝ} {F : (Fin 2 → ℝ) → ℂ}
    (hF : Integrable (triangleAmplitude χ F)) :
    cutoffDoubleIntegral χ F = localizedKernelOperator χ rectangleTimeKernel F := by
  funext t
  rw [localizedKernelOperator, cutoffKernelIntegral, integral_rectangleTimeKernel_mul hF]
  simp [cutoffDoubleIntegral, rectanglePrimitive, triangleAmplitude, coordinateCutoff,
    Fin.prod_univ_two, mul_assoc]

/-- Literal kernel identification for both orientations of the triangular source operator. -/
theorem cutoffTriangleIntegral_eq_kernel {χ : ℝ → ℝ} {F : (Fin 2 → ℝ) → ℂ}
    (hF : Integrable (triangleAmplitude χ F)) :
    cutoffTriangleIntegral χ F = localizedKernelOperator χ triangleTimeKernel F := by
  funext t
  rw [localizedKernelOperator, cutoffKernelIntegral, integral_triangleTimeKernel_mul hF]
  simp [cutoffTriangleIntegral, triangleAmplitude, coordinateCutoff,
    Fin.prod_univ_two, mul_assoc]

/-- Finite input norm gives an integrable output. -/
theorem localizedKernelOperator_integrable {p : ℝ} (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (h : CutoffControl χ)
    {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ}
    (hK : Measurable (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => K z.1 z.2))
    (hKn : ∀ t v, ‖K t v‖ ≤ 1) {F : (Fin 2 → ℝ) → ℂ}
    (hF : MemLp F (ENNReal.ofReal p)) : Integrable (localizedKernelOperator χ K F) :=
  cutoffKernelIntegral_integrable hχ.continuous h hK hKn
    (triangleAmplitude_integrable_of_memLp hp hχ h hF)

/-- Subtraction is literal on finite-norm inputs. -/
theorem localizedKernelOperator_sub {p : ℝ} (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (h : CutoffControl χ)
    {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ}
    (hK : Measurable (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => K z.1 z.2))
    (hKn : ∀ t v, ‖K t v‖ ≤ 1) {F G : (Fin 2 → ℝ) → ℂ}
    (hF : MemLp F (ENNReal.ofReal p)) (hG : MemLp G (ENNReal.ofReal p)) :
    localizedKernelOperator χ K (fun v => F v - G v) =
      fun t => localizedKernelOperator χ K F t - localizedKernelOperator χ K G t := by
  have he : triangleAmplitude χ (fun v => F v - G v) =
      fun v => triangleAmplitude χ F v - triangleAmplitude χ G v := by
    funext v
    simp only [triangleAmplitude, mul_sub]
  unfold localizedKernelOperator
  rw [he, cutoffKernelIntegral_sub hK hKn
    (triangleAmplitude_integrable_of_memLp hp hχ h hF)
    (triangleAmplitude_integrable_of_memLp hp hχ h hG)]

/-- The quantitative continuity estimate used in smooth approximation. -/
theorem eLpNorm_localizedKernelOperator_sub_one_le {p : ℝ} (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (h : CutoffControl χ)
    {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ}
    (hK : Measurable (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => K z.1 z.2))
    (hKn : ∀ t v, ‖K t v‖ ≤ 1) {F G : (Fin 2 → ℝ) → ℂ}
    (hF : MemLp F (ENNReal.ofReal p)) (hG : MemLp G (ENNReal.ofReal p)) :
    eLpNorm (fun t => localizedKernelOperator χ K F t - localizedKernelOperator χ K G t) 1 ≤
      (cutoffKernelL1Factor h.radius h.bound * localTimeL1Factor p h.radius h.bound) *
        eLpNorm (fun v => F v - G v) (ENNReal.ofReal p) := by
  rw [← localizedKernelOperator_sub hp hχ h hK hKn hF hG]
  apply (eLpNorm_cutoffKernelIntegral_one_le hχ.continuous h hK hKn
    (triangleAmplitude_integrable_of_memLp hp hχ h (hF.sub hG))).trans
  exact (mul_le_mul_right
    (eLpNorm_triangleAmplitude_one_le hp hχ h (hF.aestronglyMeasurable.sub hG.aestronglyMeasurable))
    _).trans_eq (by
      rw [mul_assoc]
      congr 1)

end WaveTurbulence.Fourier
