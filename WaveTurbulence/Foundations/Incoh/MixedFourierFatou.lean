/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.Norm00V
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Fatou passage for the mixed Fourier norm

A common bound passes to pointwise Fourier limits while keeping the
parameter supremum inside the frequency integral. No topology on the
parameter carrier is required.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace WaveTurbulence.Incoh

/-- Uniform mixed norm bounds survive pointwise Fourier convergence. -/
theorem mixedFourierNorm00_le_of_fourier_tendsto {r : ℕ} {V : Type*} (θ : ℝ)
    {F : (Fin r → ℝ) → V → ℂ} {Fₙ : ℕ → (Fin r → ℝ) → V → ℂ}
    (hF : ∀ v, Integrable (fun t => F t v))
    (hFₙ : ∀ n v, Integrable (fun t => Fₙ n t v))
    (hlim : ∀ v ξ, Tendsto (fun n => Fourier.timeFourier (fun t => Fₙ n t v) ξ)
      atTop (𝓝 (Fourier.timeFourier (fun t => F t v) ξ)))
    {C : ℝ≥0∞} (hC : ∀ n, Fourier.mixedFourierNorm00 θ (Fₙ n) ≤ C) :
    Fourier.mixedFourierNorm00 θ F ≤ C := by
  let W := fun n ξ => Fourier.timeWeight θ ξ * Fourier.mixedFourierEnvelope00 (Fₙ n) ξ
  have hm (n : ℕ) : Measurable (W n) :=
    (Fourier.timeWeight_measurable θ).mul (Fourier.measurable_mixedFourierEnvelope00 (hFₙ n))
  have hp (ξ : Fin r → ℝ) : Fourier.timeWeight θ ξ * Fourier.mixedFourierEnvelope00 F ξ ≤
      liminf (fun n => W n ξ) atTop := by
    unfold Fourier.mixedFourierEnvelope00
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro v
    have ht : Tendsto (fun n => Fourier.timeWeight θ ξ *
        ‖Fourier.timeFourier (fun t => Fₙ n t v) ξ‖ₑ) atTop
        (𝓝 (Fourier.timeWeight θ ξ * ‖Fourier.timeFourier (fun t => F t v) ξ‖ₑ)) :=
      (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).continuousAt.tendsto.comp
        (continuous_enorm.tendsto _ |>.comp (hlim v ξ))
    rw [← ht.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall (fun n => mul_le_mul' le_rfl
      (le_iSup (fun v => ‖Fourier.timeFourier (fun t => Fₙ n t v) ξ‖ₑ) v)))
  rw [Fourier.mixedFourierNorm00_eq_lintegral hF]
  apply (lintegral_mono hp).trans
  apply (lintegral_liminf_le hm).trans
  apply liminf_le_of_frequently_le'
  exact (Eventually.of_forall (fun n => by
    exact (Fourier.mixedFourierNorm00_eq_lintegral (hFₙ n)).symm.le.trans (hC n))).frequently

end WaveTurbulence.Incoh
