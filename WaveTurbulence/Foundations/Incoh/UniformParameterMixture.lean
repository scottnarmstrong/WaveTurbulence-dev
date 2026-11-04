/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FourierMixture

/-!
# Spectral mixtures controlled by a common mixed Fourier envelope

Both the root parameter and all spectral variables remain inside the
scalar-kernel supremum. This allows moving localization centers without
changing the order of the source norm.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Conditional transport of a uniform parameter-family bound through an integrable mixture. -/
theorem mixedFourierNorm00_integral_uniform_parameter_le {r : ℕ} {U V : Type*}
    [MeasurableSpace U] (μ : Measure U) [SFinite μ] (θ : ℝ)
    (A : V → U → ℂ) (K : (Fin r → ℝ) → V → U → ℂ)
    (hiK : ∀ v u, Integrable (fun t => K t v u))
    (hjoint : ∀ v, Integrable (fun z : (Fin r → ℝ) × U => A v z.2 * K z.1 v z.2) (volume.prod μ))
    {E : U → ℝ≥0∞} (hE : Measurable E) (hA : ∀ v u, ‖A v u‖ₑ ≤ E u) :
    Fourier.mixedFourierNorm00 θ (fun t v => ∫ u, A v u * K t v u ∂μ) ≤
      (∫⁻ u, E u ∂μ) * Fourier.mixedFourierNorm00 θ (fun t (p : V × U) => K t p.1 p.2) := by
  let G := fun t : Fin r → ℝ => fun p : V × U => K t p.1 p.2
  have hiG (p : V × U) : Integrable (fun t => G t p) := hiK p.1 p.2
  have hiF (v : V) : Integrable (fun t => ∫ u, A v u * K t v u ∂μ) := (hjoint v).integral_prod_left
  have henv := Fourier.measurable_mixedFourierEnvelope00 hiG
  have hp (ξ : Fin r → ℝ) :
      Fourier.mixedFourierEnvelope00 (fun t v => ∫ u, A v u * K t v u ∂μ) ξ ≤
        (∫⁻ u, E u ∂μ) * Fourier.mixedFourierEnvelope00 G ξ := by
    apply iSup_le
    intro v
    have he := timeFourier_integral_mixture μ (A v) (fun u => (v, u)) G (hjoint v) ξ
    rw [he]
    apply (enorm_integral_le_lintegral_enorm _).trans
    calc
      _ ≤ ∫⁻ u, E u * Fourier.mixedFourierEnvelope00 G ξ ∂μ := by
        apply lintegral_mono
        intro u
        dsimp only
        rw [enorm_mul]
        exact mul_le_mul' (hA v u)
          (le_iSup (fun p : V × U => ‖Fourier.timeFourier (fun t => G t p) ξ‖ₑ) (v, u))
      _ = _ := lintegral_mul_const _ hE
  rw [Fourier.mixedFourierNorm00_eq_lintegral hiF, Fourier.mixedFourierNorm00_eq_lintegral hiG]
  calc
    _ ≤ ∫⁻ ξ, Fourier.timeWeight θ ξ *
        ((∫⁻ u, E u ∂μ) * Fourier.mixedFourierEnvelope00 G ξ) :=
      lintegral_mono (fun ξ => mul_le_mul' le_rfl (hp ξ))
    _ = ∫⁻ ξ, (∫⁻ u, E u ∂μ) *
        (Fourier.timeWeight θ ξ * Fourier.mixedFourierEnvelope00 G ξ) := by
      apply lintegral_congr
      intro ξ
      ring
    _ = _ := lintegral_const_mul _ ((Fourier.timeWeight_measurable θ).mul henv)

/-- Conditional transport using only a uniform actual amplitude mass. The localization
support may move with the vector parameter; no common pointwise spectral envelope is required. -/
theorem mixedFourierNorm00_integral_uniform_mass_le {r : ℕ} {U V : Type*}
    [MeasurableSpace U] (μ : Measure U) [SFinite μ] (θ : ℝ)
    (A : V → U → ℂ) (K : (Fin r → ℝ) → V → U → ℂ)
    (hA : ∀ v, StronglyMeasurable (A v))
    (hiK : ∀ v u, Integrable (fun t => K t v u))
    (hjoint : ∀ v, Integrable (fun z : (Fin r → ℝ) × U => A v z.2 * K z.1 v z.2) (volume.prod μ))
    {M : ℝ≥0∞} (hM : ∀ v, (∫⁻ u, ‖A v u‖ₑ ∂μ) ≤ M) :
    Fourier.mixedFourierNorm00 θ (fun t v => ∫ u, A v u * K t v u ∂μ) ≤
      M * Fourier.mixedFourierNorm00 θ (fun t (p : V × U) => K t p.1 p.2) := by
  let G := fun t : Fin r → ℝ => fun p : V × U => K t p.1 p.2
  have hiG (p : V × U) : Integrable (fun t => G t p) := hiK p.1 p.2
  have hiF (v : V) : Integrable (fun t => ∫ u, A v u * K t v u ∂μ) := (hjoint v).integral_prod_left
  have henv := Fourier.measurable_mixedFourierEnvelope00 hiG
  have hp (ξ : Fin r → ℝ) :
      Fourier.mixedFourierEnvelope00 (fun t v => ∫ u, A v u * K t v u ∂μ) ξ ≤
        M * Fourier.mixedFourierEnvelope00 G ξ := by
    apply iSup_le
    intro v
    have he := timeFourier_integral_mixture μ (A v) (fun u => (v, u)) G (hjoint v) ξ
    rw [he]
    apply (enorm_integral_le_lintegral_enorm _).trans
    calc
      _ ≤ ∫⁻ u, ‖A v u‖ₑ * Fourier.mixedFourierEnvelope00 G ξ ∂μ := by
        apply lintegral_mono
        intro u
        dsimp only
        rw [enorm_mul]
        exact mul_le_mul' le_rfl
          (le_iSup (fun p : V × U => ‖Fourier.timeFourier (fun t => G t p) ξ‖ₑ) (v, u))
      _ = (∫⁻ u, ‖A v u‖ₑ ∂μ) * Fourier.mixedFourierEnvelope00 G ξ :=
        lintegral_mul_const _ (hA v).measurable.enorm
      _ ≤ _ := mul_le_mul' (hM v) le_rfl
  rw [Fourier.mixedFourierNorm00_eq_lintegral hiF, Fourier.mixedFourierNorm00_eq_lintegral hiG]
  calc
    _ ≤ ∫⁻ ξ, Fourier.timeWeight θ ξ * (M * Fourier.mixedFourierEnvelope00 G ξ) :=
      lintegral_mono (fun ξ => mul_le_mul' le_rfl (hp ξ))
    _ = ∫⁻ ξ, M * (Fourier.timeWeight θ ξ * Fourier.mixedFourierEnvelope00 G ξ) := by
      apply lintegral_congr
      intro ξ
      ring
    _ = _ := lintegral_const_mul _ ((Fourier.timeWeight_measurable θ).mul henv)

end WaveTurbulence.Incoh
