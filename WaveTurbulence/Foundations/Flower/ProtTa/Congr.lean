/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib
public import WaveTurbulence.Foundations.Fourier.Norm00V

/-! # PROT-TA: `mixedFourierNorm00` only sees almost-everywhere classes of the slices -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtTa

theorem timeFourier_congr_ae {r : ℕ} {f g : (Fin r → ℝ) → ℂ} (h : f =ᵐ[volume] g) :
    timeFourier f = timeFourier g := by
  funext ξ
  unfold timeFourier VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards [h] with t ht
  simp only [ht]

theorem mixedFourierNorm00_congr_ae {r : ℕ} {V : Type*} {θ : ℝ} {F G : (Fin r → ℝ) → V → ℂ}
    (h : ∀ v, (fun t => F t v) =ᵐ[volume] fun t => G t v) :
    mixedFourierNorm00 θ F = mixedFourierNorm00 θ G := by
  by_cases hF : ∀ v, Integrable (fun t => F t v)
  · have hG : ∀ v, Integrable (fun t => G t v) := fun v => (integrable_congr (h v)).mp (hF v)
    rw [mixedFourierNorm00_eq_lintegral hF, mixedFourierNorm00_eq_lintegral hG]
    congr 1
    funext ξ
    simp only [mixedFourierEnvelope00, timeFourier_congr_ae (h _)]
  · have hG : ¬ ∀ v, Integrable (fun t => G t v) := fun hG =>
      hF fun v => (integrable_congr (h v)).mpr (hG v)
    rw [mixedFourierNorm00_of_not_integrable hF, mixedFourierNorm00_of_not_integrable hG]

end WaveTurbulence.Flower.ProtTa
