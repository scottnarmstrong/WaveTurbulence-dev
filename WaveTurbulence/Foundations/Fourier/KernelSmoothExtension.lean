/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.KernelSmoothApproximation
public import WaveTurbulence.Foundations.Fourier.WeightedFourierClosure
import Mathlib.Tactic

/-!
# Extending proved smooth bounds for localized time kernels

These are generic closure lemmas. The source-facing A.2 results separately
supply the literal kernels and the already proved smooth estimates.
-/

public section

open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

namespace WaveTurbulence.Fourier

/-- A weighted Fourier-norm bound on smooth compact inputs extends to every finite-norm input. -/
theorem timeFourierNorm_localizedKernel_le_of_smooth_bound {p : ℝ} (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (h : CutoffControl χ)
    {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ}
    (hK : Measurable (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => K z.1 z.2))
    (hKn : ∀ t v, ‖K t v‖ ≤ 1) (θ : ℝ) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ g : (Fin 2 → ℝ) → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
      timeFourierNorm θ (localizedKernelOperator χ K g) ≤ C * eLpNorm g (ENNReal.ofReal p))
    {F : (Fin 2 → ℝ) → ℂ} (hF : MemLp F (ENNReal.ofReal p)) :
    timeFourierNorm θ (localizedKernelOperator χ K F) ≤ C * eLpNorm F (ENNReal.ofReal p) := by
  obtain ⟨g, hgs, hgc, hgn, hlim⟩ := exists_localizedKernel_smooth_approximation hp hχ h hK hKn hF
  have hgi (n : ℕ) : Integrable (localizedKernelOperator χ K (g n)) :=
    localizedKernelOperator_integrable hp hχ h hK hKn
      ((hgs n).continuous.memLp_of_hasCompactSupport (hgc n))
  apply timeFourierNorm_le_of_approximation_bound θ
    (localizedKernelOperator_integrable hp hχ h hK hKn hF) hgi hlim hC
    tendsto_smoothApproximationError
  intro n
  exact (hbound (g n) (hgs n) (hgc n)).trans (mul_le_mul_right (hgn n) C)

/-- A pointwise weighted Fourier estimate extends as well; the frequency remains fixed in this closure step. -/
theorem weighted_fourier_localizedKernel_le_of_smooth_bound {p : ℝ} (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (h : CutoffControl χ)
    {K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ}
    (hK : Measurable (fun z : (Fin 2 → ℝ) × (Fin 2 → ℝ) => K z.1 z.2))
    (hKn : ∀ t v, ‖K t v‖ ≤ 1) (ξ : Fin 2 → ℝ)
    {w C : ℝ≥0∞} (hw : w ≠ ⊤) (hC : C ≠ ⊤)
    (hbound : ∀ g : (Fin 2 → ℝ) → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
      w * ‖timeFourier (localizedKernelOperator χ K g) ξ‖ₑ ≤ C * eLpNorm g (ENNReal.ofReal p))
    {F : (Fin 2 → ℝ) → ℂ} (hF : MemLp F (ENNReal.ofReal p)) :
    w * ‖timeFourier (localizedKernelOperator χ K F) ξ‖ₑ ≤ C * eLpNorm F (ENNReal.ofReal p) := by
  obtain ⟨g, hgs, hgc, hgn, hlim⟩ := exists_localizedKernel_smooth_approximation hp hχ h hK hKn hF
  have hlower := ENNReal.Tendsto.const_mul (hlim ξ).enorm (Or.inr hw)
  have hupper : Tendsto (fun n => C * (eLpNorm F (ENNReal.ofReal p) + smoothApproximationError n))
      atTop (𝓝 (C * eLpNorm F (ENNReal.ofReal p))) := by
    simpa only [add_zero] using ENNReal.Tendsto.const_mul
      (tendsto_const_nhds.add tendsto_smoothApproximationError) (Or.inr hC)
  exact le_of_tendsto_of_tendsto hlower hupper (Eventually.of_forall fun n =>
    (hbound (g n) (hgs n) (hgc n)).trans (mul_le_mul_right (hgn n) C))

end WaveTurbulence.Fourier
