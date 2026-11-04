/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FourierMixture

/-!
# Mixed Fourier bounds for internal-clock mixtures

The universal kernel envelope is taken before integrating the internal
amplitude, so the bound retains the required order of the momentum supremum.
This is a generic Fubini inequality, not a source carrier estimate field.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- An actual integral mixture costs only its amplitude's absolute mass. -/
theorem mixedFourierNorm00_integral_mixture_le {r : ℕ} {U V W : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] (θ : ℝ) (A : V → U → ℂ) (p : V → U → W)
    (K : (Fin r → ℝ) → W → ℂ) (hK : ∀ w, Integrable (fun t => K t w))
    (hA : ∀ v, AEStronglyMeasurable (A v) μ)
    (hjoint : ∀ v, Integrable (fun z : (Fin r → ℝ) × U => A v z.2 * K z.1 (p v z.2))
      (volume.prod μ)) {M : ℝ≥0∞} (hmass : ∀ v, (∫⁻ u, ‖A v u‖ₑ ∂μ) ≤ M) :
    Fourier.mixedFourierNorm00 θ (fun t v => ∫ u, A v u * K t (p v u) ∂μ) ≤
      M * Fourier.mixedFourierNorm00 θ K := by
  have hG (v : V) : Integrable (fun t => ∫ u, A v u * K t (p v u) ∂μ) :=
    (hjoint v).integral_prod_left
  have hp (ξ : Fin r → ℝ) :
      Fourier.mixedFourierEnvelope00 (fun t v => ∫ u, A v u * K t (p v u) ∂μ) ξ ≤
        M * Fourier.mixedFourierEnvelope00 K ξ := by
    apply iSup_le
    intro v
    rw [timeFourier_integral_mixture μ (A v) (p v) K (hjoint v)]
    calc
      _ ≤ ∫⁻ u, ‖A v u * Fourier.timeFourier (fun t => K t (p v u)) ξ‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ u, ‖A v u‖ₑ * Fourier.mixedFourierEnvelope00 K ξ ∂μ := by
        apply lintegral_mono
        intro u
        dsimp only
        rw [enorm_mul]
        exact mul_le_mul' le_rfl
          (le_iSup (fun w => ‖Fourier.timeFourier (fun t => K t w) ξ‖ₑ) (p v u))
      _ = (∫⁻ u, ‖A v u‖ₑ ∂μ) * Fourier.mixedFourierEnvelope00 K ξ :=
        lintegral_mul_const'' _ (hA v).enorm
      _ ≤ _ := mul_le_mul' (hmass v) le_rfl
  rw [Fourier.mixedFourierNorm00_eq_lintegral hG, Fourier.mixedFourierNorm00_eq_lintegral hK]
  calc
    _ ≤ ∫⁻ ξ, Fourier.timeWeight θ ξ * (M * Fourier.mixedFourierEnvelope00 K ξ) :=
      lintegral_mono (fun ξ => mul_le_mul' le_rfl (hp ξ))
    _ = ∫⁻ ξ, M * (Fourier.timeWeight θ ξ * Fourier.mixedFourierEnvelope00 K ξ) := by
      apply lintegral_congr
      intro ξ
      ac_rfl
    _ = _ := lintegral_const_mul _ ((Fourier.timeWeight_measurable θ).mul
      (Fourier.measurable_mixedFourierEnvelope00 hK))

end WaveTurbulence.Incoh
