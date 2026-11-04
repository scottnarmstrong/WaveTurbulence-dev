/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LocalModelSpectralIntegral
public import WaveTurbulence.Foundations.Incoh.FourierMixture
public import WaveTurbulence.Foundations.Incoh.FourierFamilyMeasurable
public import WaveTurbulence.Foundations.Incoh.MixedSpatialEnvelope
public import WaveTurbulence.Foundations.Fourier.TimeFourierLimit

/-! # Full spatial mixed norms from local models and uniform actual derivative mass

This conditional transport retains all scalar kernel parameters inside
the common Fourier envelope, as required by the tree's lone leaf.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

namespace WaveTurbulence.Incoh

/-- Conditional full-spatial transport through a locally modelled actual amplitude. The uniform
mass is on actual derivatives. Scalar kernels remain inside one common Fourier supremum. -/
theorem mixedFourierNorm_localModel_uniformMass_le {r d N : ℕ} {U : Type*}
    [MeasurableSpace U] (μ : Measure U) [SFinite μ] (θ : ℝ)
    (A : Mom d → U → ℂ) (A₀ : Mom d → Mom d → U → ℂ) (v : Mom d → ℕ → U → ℝ)
    (hloc : ∀ p, ∀ᶠ k in 𝓝 p, ∀ u, A k u = A₀ p k u)
    (hA₀ : ∀ p u, ContDiff ℝ N (fun k => A₀ p k u))
    (hm : ∀ p j, j ≤ N → ∀ k, StronglyMeasurable
      (fun u => iteratedFDeriv ℝ j (fun k => A₀ p k u) k))
    (hv : ∀ p j, j ≤ N → Integrable (v p j) μ)
    (hb : ∀ p j, j ≤ N → ∀ k u, ‖iteratedFDeriv ℝ j (fun k => A₀ p k u) k‖ ≤ v p j u)
    (K : (Fin r → ℝ) → U → ℂ)
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × U => K z.1 z.2))
    (hiK : ∀ u, Integrable (fun t => K t u))
    (hjoint : ∀ k, Integrable (fun z : (Fin r → ℝ) × U => A k z.2 * K z.1 z.2) (volume.prod μ))
    {H : ℝ≥0∞} (hH : H < ⊤) (hphys : ∀ u, eLpNorm (fun t => K t u) 1 ≤ H)
    {M : ℝ≥0∞} (hmass : ∀ j ≤ N, ∀ k,
      (∫⁻ u, ‖iteratedFDeriv ℝ j (fun k => A k u) k‖ₑ ∂μ) ≤ M) :
    Fourier.mixedFourierNorm θ N 0 (fun t k => ∫ u, A k u * K t u ∂μ) ≤
      M * Fourier.mixedFourierNorm00 θ K := by
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
    have ht := timeFourier_integral_mixture μ (A k) id K (hjoint k) ξ
    dsimp only [id_eq] at ht
    change Fourier.timeFourier (fun t => ∫ u, A k u * K t u ∂μ) ξ = _
    rw [ht]
    exact integral_congr_ae (ae_of_all _ (fun u => by dsimp only [ψ]; ring))
  have hs (ξ : Fin r → ℝ) := localModel_spectralIntegral_derivatives μ A A₀ v hloc hA₀
    (fun p j hj k => (hm p j hj k).aestronglyMeasurable) hv hb (ψ ξ) (hmψ ξ) ENNReal.toReal_nonneg (hbψ ξ)
  have hCF (ξ : Fin r → ℝ) : ContDiff ℝ N (Fourier.mixedTimeFourier F ξ) := by
    rw [he]
    exact (hs ξ).1
  have hDF (ξ : Fin r → ℝ) (j : ℕ) (hj : j ≤ N) (k : Mom d) :
      iteratedFDeriv ℝ j (Fourier.mixedTimeFourier F ξ) k =
        ∫ u, ψ ξ u • iteratedFDeriv ℝ j (fun k => A k u) k ∂μ := by
    rw [he]
    exact (hs ξ).2 j hj k
  have hDm (j : ℕ) (hj : j ≤ N) (k : Mom d) :
      StronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun k => A k u) k) := by
    have heq (u : U) : iteratedFDeriv ℝ j (fun k => A k u) k =
        iteratedFDeriv ℝ j (fun k' => A₀ k k' u) k := by
      have hevent : (fun k' => A k' u) =ᶠ[𝓝 k] (fun k' => A₀ k k' u) :=
        (hloc k).mono (fun k' hk' => hk' u)
      exact (hevent.iteratedFDeriv ℝ j).self_of_nhds
    simp_rw [heq]
    exact hm k j hj k
  have hguard : Fourier.MixedFourierAdmissible N F :=
    ⟨fun k => (hjoint k).integral_prod_left, Or.inr (ae_of_all _ hCF)⟩
  rw [Fourier.mixedFourierNorm, ite_eq_left hguard]
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  apply iSup_le
  intro ρ
  have hp (ξ : Fin r → ℝ) : Fourier.momentumSupNorm 0
      (Fourier.momentumDerivative ρ (Fourier.mixedTimeFourier F ξ)) ≤
        M * Fourier.mixedFourierEnvelope00 K ξ := by
    unfold Fourier.momentumSupNorm
    simp only [pow_zero, ENNReal.ofReal_one, one_mul]
    apply iSup_le
    intro k
    have hc : ‖Fourier.momentumDerivative ρ (Fourier.mixedTimeFourier F ξ) k‖ ≤
        ‖iteratedFDeriv ℝ j (Fourier.mixedTimeFourier F ξ) k‖ := by
      simpa only [Fourier.momentumDerivative, EuclideanSpace.single, PiLp.norm_single,
        norm_one, Finset.prod_const_one, mul_one] using
        (iteratedFDeriv ℝ j (Fourier.mixedTimeFourier F ξ) k).le_opNorm
          (fun i => EuclideanSpace.single (ρ i) 1)
    have hce : ‖Fourier.momentumDerivative ρ (Fourier.mixedTimeFourier F ξ) k‖ₑ ≤
        ‖iteratedFDeriv ℝ j (Fourier.mixedTimeFourier F ξ) k‖ₑ := by
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hc
    apply hce.trans
    rw [hDF ξ j hj k]
    apply (enorm_integral_le_lintegral_enorm _).trans
    calc
      _ ≤ ∫⁻ u, Fourier.mixedFourierEnvelope00 K ξ * ‖iteratedFDeriv ℝ j (fun k => A k u) k‖ₑ ∂μ := by
        apply lintegral_mono
        intro u
        dsimp only
        rw [enorm_smul]
        exact mul_le_mul' (le_iSup (fun u => ‖Fourier.timeFourier (fun t => K t u) ξ‖ₑ) u) le_rfl
      _ = Fourier.mixedFourierEnvelope00 K ξ *
          ∫⁻ u, ‖iteratedFDeriv ℝ j (fun k => A k u) k‖ₑ ∂μ :=
        lintegral_const_mul _ (continuous_enorm.comp_stronglyMeasurable (hDm j hj k)).measurable
      _ ≤ _ := by simpa only [mul_comm] using mul_le_mul' le_rfl (hmass j hj k)
  rw [Fourier.mixedFourierNorm00_eq_lintegral hiK]
  calc
    _ ≤ ∫⁻ ξ, Fourier.timeWeight θ ξ * (M * Fourier.mixedFourierEnvelope00 K ξ) :=
      lintegral_mono (fun ξ => mul_le_mul' le_rfl (hp ξ))
    _ = ∫⁻ ξ, M * (Fourier.timeWeight θ ξ * Fourier.mixedFourierEnvelope00 K ξ) := by
      apply lintegral_congr
      intro ξ
      ring
    _ = _ := lintegral_const_mul _ ((Fourier.timeWeight_measurable θ).mul
      (Fourier.measurable_mixedFourierEnvelope00 hiK))

end WaveTurbulence.Incoh
