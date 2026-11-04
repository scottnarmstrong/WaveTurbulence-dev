/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FourierFamilyMeasurable

/-!
# A dominated Fourier mixture inequality

A common pointwise amplitude envelope may be integrated against the
individual kernel Fourier norms. Unlike an absolute mass bound, this
retains frequency weights of the parameter being integrated.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The mixed norm of an actual mixture is bounded by the envelope-weighted
integral of its scalar kernel norms. -/
theorem mixedFourierNorm00_integral_dominated_le {r : ℕ} {U V : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] (θ : ℝ) (A : V → U → ℂ)
    (K : (Fin r → ℝ) → U → ℂ)
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × U => K z.1 z.2))
    (hiK : ∀ u, Integrable (fun t => K t u))
    (hjoint : ∀ v, Integrable (fun z : (Fin r → ℝ) × U => A v z.2 * K z.1 z.2) (volume.prod μ))
    {E : U → ℝ≥0∞} (hE : Measurable E) (hA : ∀ v u, ‖A v u‖ₑ ≤ E u) :
    Fourier.mixedFourierNorm00 θ (fun t v => ∫ u, A v u * K t u ∂μ) ≤
      ∫⁻ u, E u * Fourier.timeFourierNorm θ (fun t => K t u) ∂μ := by
  have hG (v : V) : Integrable (fun t => ∫ u, A v u * K t u ∂μ) :=
    (hjoint v).integral_prod_left
  have hhat := (stronglyMeasurable_timeFourier_family hK).measurable.enorm
  have hp (ξ : Fin r → ℝ) :
      Fourier.mixedFourierEnvelope00 (fun t v => ∫ u, A v u * K t u ∂μ) ξ ≤
        ∫⁻ u, E u * ‖Fourier.timeFourier (fun t => K t u) ξ‖ₑ ∂μ := by
    apply iSup_le
    intro v
    have he := timeFourier_integral_mixture μ (A v) id K (hjoint v) ξ
    dsimp only [id_eq] at he
    dsimp only
    rw [he]
    apply (enorm_integral_le_lintegral_enorm _).trans
    apply lintegral_mono
    intro u
    dsimp only [id_eq]
    rw [enorm_mul]
    exact mul_le_mul' (hA v u) le_rfl
  have hm : Measurable (fun z : (Fin r → ℝ) × U =>
      Fourier.timeWeight θ z.1 * (E z.2 * ‖Fourier.timeFourier (fun t => K t z.2) z.1‖ₑ)) :=
    ((Fourier.timeWeight_measurable θ).comp measurable_fst).mul
      ((hE.comp measurable_snd).mul hhat)
  rw [Fourier.mixedFourierNorm00_eq_lintegral hG]
  calc
    _ ≤ ∫⁻ ξ, Fourier.timeWeight θ ξ *
        (∫⁻ u, E u * ‖Fourier.timeFourier (fun t => K t u) ξ‖ₑ ∂μ) :=
      lintegral_mono (fun ξ => mul_le_mul' le_rfl (hp ξ))
    _ = ∫⁻ ξ, ∫⁻ u, Fourier.timeWeight θ ξ *
        (E u * ‖Fourier.timeFourier (fun t => K t u) ξ‖ₑ) ∂μ := by
      apply lintegral_congr
      intro ξ
      exact (lintegral_const_mul _
        (hE.mul (hhat.comp (measurable_const.prodMk measurable_id)))).symm
    _ = ∫⁻ u, ∫⁻ ξ, Fourier.timeWeight θ ξ *
        (E u * ‖Fourier.timeFourier (fun t => K t u) ξ‖ₑ) ∂volume ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro u
      rw [Fourier.timeFourierNorm_eq_lintegral (hiK u)]
      have hmm : Measurable (fun ξ => Fourier.timeWeight θ ξ *
          ‖Fourier.timeFourier (fun t => K t u) ξ‖ₑ) :=
        (Fourier.timeWeight_measurable θ).mul
          (Fourier.timeFourier_continuous (hiK u)).measurable.enorm
      calc
        _ = ∫⁻ ξ, E u * (Fourier.timeWeight θ ξ * ‖Fourier.timeFourier (fun t => K t u) ξ‖ₑ) := by
          apply lintegral_congr
          intro ξ
          ac_rfl
        _ = _ := lintegral_const_mul _ hmm

end WaveTurbulence.Incoh
