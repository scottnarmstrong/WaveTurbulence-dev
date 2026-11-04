/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpatialSpectralIntegral
public import WaveTurbulence.Foundations.Incoh.MixedSpatialEnvelope
public import WaveTurbulence.Foundations.Incoh.DominatedFourierMixture
public import WaveTurbulence.Foundations.Fourier.TimeFourierLimit

/-! # Full spatial mixed norms of actual spectral mixtures

Conditional transport for Proposition 5.1. The amplitude's actual spatial
derivatives have an integrable common envelope. No analytic kernel norm
is moved into a carrier field; the final source applications supply it.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- Full weighted spatial/time norm transport, preserving the source order of supremum and
frequency integration. All differentiations are of the actual spectral integral. -/
theorem mixedFourierNorm_spectralMixture_le {r d N M : ℕ} {U : Type*}
    [MeasurableSpace U] (μ : Measure U) [SFinite μ] (θ : ℝ)
    (A : Mom d → U → ℂ) (v : U → ℝ) (K : (Fin r → ℝ) → U → ℂ)
    (hA : ∀ u, ContDiff ℝ N (fun k => A k u))
    (hmeas : ∀ j ≤ N, ∀ k, AEStronglyMeasurable
      (fun u => iteratedFDeriv ℝ j (fun k => A k u) k) μ)
    (hv : Integrable v μ) (hvm : Measurable v) (hvn : ∀ u, 0 ≤ v u)
    (hb : ∀ j ≤ N, ∀ k u, Fourier.momentumBracket k ^ M *
      ‖iteratedFDeriv ℝ j (fun k => A k u) k‖ ≤ v u)
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × U => K z.1 z.2))
    (hiK : ∀ u, Integrable (fun t => K t u))
    (hjoint : ∀ k, Integrable (fun z : (Fin r → ℝ) × U => A k z.2 * K z.1 z.2) (volume.prod μ))
    {H : ℝ≥0∞} (hH : H < ⊤) (hphys : ∀ u, eLpNorm (fun t => K t u) 1 ≤ H) :
    Fourier.mixedFourierNorm θ N M (fun t k => ∫ u, A k u * K t u ∂μ) ≤
      ∫⁻ u, ENNReal.ofReal (v u) * Fourier.timeFourierNorm θ (fun t => K t u) ∂μ := by
  let F := fun t k => ∫ u, A k u * K t u ∂μ
  let ψ := fun ξ u => Fourier.timeFourier (fun t => K t u) ξ
  have hψ := stronglyMeasurable_timeFourier_family hK
  have hmψ (ξ : Fin r → ℝ) : AEStronglyMeasurable (ψ ξ) μ :=
    (hψ.comp_measurable (g := fun u => (ξ, u)) (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hbψ (ξ : Fin r → ℝ) (u : U) : ‖ψ ξ u‖ ≤ H.toReal := by
    have hh := (Fourier.enorm_timeFourier_le_eLpNorm_one (fun t => K t u) ξ).trans (hphys u)
    simpa only [toReal_enorm] using ENNReal.toReal_mono hH.ne hh
  have he (ξ : Fin r → ℝ) : Fourier.mixedTimeFourier F ξ = fun k => ∫ u, ψ ξ u * A k u ∂μ := by
    funext k
    change Fourier.timeFourier (fun t => ∫ u, A k u * K t u ∂μ) ξ = _
    have ht := timeFourier_integral_mixture μ (A k) id K (hjoint k) ξ
    dsimp only [id_eq] at ht
    rw [ht]
    apply integral_congr_ae
    exact ae_of_all _ (fun u => by dsimp only [ψ, id_eq]; ring)
  have hSF (ξ : Fin r → ℝ) : Fourier.spatialNorm N M (Fourier.mixedTimeFourier F ξ) ≤
      ∫⁻ u, ENNReal.ofReal (v u) * ‖ψ ξ u‖ₑ ∂μ := by
    rw [he]
    exact spatialNorm_spectralIntegral_le μ A v (ψ ξ) hA hmeas hv hvn hb (hmψ ξ) (hbψ ξ)
  have hfinite (ξ : Fin r → ℝ) : (∫⁻ u, ENNReal.ofReal (v u) * ‖ψ ξ u‖ₑ ∂μ) < ⊤ := by
    have hi : Integrable (fun u => ‖ψ ξ u‖ * v u) μ :=
      hv.bdd_mul (hmψ ξ).norm (ae_of_all _ (fun u => by simpa only [norm_norm] using hbψ ξ u))
    have heq : (∫⁻ u, ENNReal.ofReal (v u) * ‖ψ ξ u‖ₑ ∂μ) =
        ENNReal.ofReal (∫ u, ‖ψ ξ u‖ * v u ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun u => mul_nonneg (norm_nonneg _) (hvn u)))]
      apply lintegral_congr
      intro u
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, mul_comm]
    rw [heq]
    exact ENNReal.ofReal_lt_top
  have hguard : Fourier.MixedFourierAdmissible N F := by
    refine ⟨fun k => (hjoint k).integral_prod_left, ?_⟩
    by_cases hN : N = 0
    · exact Or.inl hN
    · exact Or.inr (ae_of_all _ (fun ξ => contDiff_of_spatialNorm_lt_top (Nat.pos_of_ne_zero hN)
        ((hSF ξ).trans_lt (hfinite ξ))))
  apply (mixedFourierNorm_le_lintegral_spatialNorm θ F hguard).trans
  apply (lintegral_mono (fun ξ => mul_le_mul' le_rfl (hSF ξ))).trans_eq
  have hm : Measurable (fun z : (Fin r → ℝ) × U => Fourier.timeWeight θ z.1 *
      (ENNReal.ofReal (v z.2) * ‖ψ z.1 z.2‖ₑ)) :=
    ((Fourier.timeWeight_measurable θ).comp measurable_fst).mul
      (((ENNReal.measurable_ofReal.comp hvm).comp measurable_snd).mul hψ.measurable.enorm)
  calc
    _ = ∫⁻ ξ, ∫⁻ u, Fourier.timeWeight θ ξ * (ENNReal.ofReal (v u) * ‖ψ ξ u‖ₑ) ∂μ := by
      apply lintegral_congr
      intro ξ
      exact (lintegral_const_mul _ ((ENNReal.measurable_ofReal.comp hvm).mul
        (hψ.measurable.comp (measurable_const.prodMk measurable_id)).enorm)).symm
    _ = ∫⁻ u, ∫⁻ ξ, Fourier.timeWeight θ ξ * (ENNReal.ofReal (v u) * ‖ψ ξ u‖ₑ) ∂volume ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro u
      rw [Fourier.timeFourierNorm_eq_lintegral (hiK u)]
      have ht : Measurable (fun ξ => Fourier.timeWeight θ ξ * ‖ψ ξ u‖ₑ) :=
        (Fourier.timeWeight_measurable θ).mul (Fourier.timeFourier_continuous (hiK u)).measurable.enorm
      calc
        _ = ∫⁻ ξ, ENNReal.ofReal (v u) * (Fourier.timeWeight θ ξ * ‖ψ ξ u‖ₑ) := by
          apply lintegral_congr
          intro ξ
          ring
        _ = _ := lintegral_const_mul _ ht

end WaveTurbulence.Incoh
