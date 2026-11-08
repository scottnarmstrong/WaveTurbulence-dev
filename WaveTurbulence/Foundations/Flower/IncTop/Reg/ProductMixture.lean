/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.FrequencyTranslation
public import WaveTurbulence.Foundations.Incoh.SpectralSpatialMixture
public import WaveTurbulence.Foundations.Incoh.UniformL1MixtureIntegrability
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.RootAmplitudeMixture

/-! Ported by source from C2-B-TOP `Cut2BReg.ProductMixture` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Full spatial norm transport on a product Fourier measure

The Fourier parameter is integrated together with the source spectral
variables. Root derivatives therefore fall only on the source amplitude.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open Cut2A

/-- A root-independent scalar multiplies every actual amplitude jet by that scalar. -/
theorem iteratedFDeriv_mul_amplitude {d j : ℕ} (A : Mom d → ℂ) (c : ℂ)
    (hA : ContDiff ℝ j A) (k : Mom d) :
    iteratedFDeriv ℝ j (fun k => c * A k) k = c • iteratedFDeriv ℝ j A k :=
  by simpa only [smul_eq_mul] using (iteratedFDeriv_const_smul_apply' (a := c) hA.contDiffAt)

/-- Conditional analytic transport for product spectral/character measures, at full root
orders. Applications below supply the actual source amplitudes and link kernels. -/
theorem mixedFourierNorm_productMixture_le {r d N M : ℕ} {U V α : Type*}
    [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace α]
    (μ : Measure U) [SFinite μ] (F : SpatialMeasure V α) (hamp : Measurable F.amplitude)
    (θ : ℝ) (A : Mom d → U → ℂ) (v : U → ℝ) (K : (Fin r → ℝ) → U × α → ℂ)
    (hA : ∀ u, ContDiff ℝ N (fun k => A k u))
    (hm : ∀ j ≤ N, ∀ k, StronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun k => A k u) k))
    (hv : Integrable v μ) (hvm : Measurable v) (hvn : ∀ u, 0 ≤ v u)
    (hb : ∀ j ≤ N, ∀ k u, Fourier.momentumBracket k ^ M *
      ‖iteratedFDeriv ℝ j (fun k => A k u) k‖ ≤ v u)
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × (U × α) => K z.1 z.2))
    (hiK : ∀ u, Integrable (fun t => K t u))
    {H : ℝ≥0∞} (hH : H < ⊤) (hphys : ∀ u, eLpNorm (fun t => K t u) 1 ≤ H)
    {Z : ℝ≥0∞} (hdecay : ∀ u, Fourier.timeFourierNorm θ (fun t => K t u) ≤ Z) :
    Fourier.mixedFourierNorm θ N M
      (fun t k => ∫ u, F.amplitude u.2 * A k u.1 * K t u ∂μ.prod F.μ) ≤
        ((∫⁻ u, ENNReal.ofReal (v u) ∂μ) * ENNReal.ofReal F.mass) * Z := by
  let A' := fun k (u : U × α) => F.amplitude u.2 * A k u.1
  let v' := fun u : U × α => v u.1 * ‖F.amplitude u.2‖
  have hs (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U × α) :
      iteratedFDeriv ℝ j (fun k => A' k u) k =
        F.amplitude u.2 • iteratedFDeriv ℝ j (fun k => A k u.1) k :=
    iteratedFDeriv_mul_amplitude _ _ ((hA u.1).of_le (by exact_mod_cast hj)) k
  have hm' (j : ℕ) (hj : j ≤ N) (k : Mom d) :
      StronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun k => A' k u) k) := by
    simp_rw [hs j hj k]
    exact (hamp.comp measurable_snd).stronglyMeasurable.smul ((hm j hj k).comp_measurable measurable_fst)
  have hv' : Integrable v' (μ.prod F.μ) := hv.mul_prod F.amplitude_integrable.norm
  have hvm' : Measurable v' := (hvm.comp measurable_fst).mul (hamp.norm.comp measurable_snd)
  have hvn' (u : U × α) : 0 ≤ v' u := mul_nonneg (hvn _) (norm_nonneg _)
  have hb' (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U × α) :
      Fourier.momentumBracket k ^ M * ‖iteratedFDeriv ℝ j (fun k => A' k u) k‖ ≤ v' u := by
    rw [hs j hj k u, norm_smul]
    change _ ≤ v u.1 * ‖F.amplitude u.2‖
    calc
      _ = (Fourier.momentumBracket k ^ M *
        ‖iteratedFDeriv ℝ j (fun k => A k u.1) k‖) * ‖F.amplitude u.2‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb j hj k u.1) (norm_nonneg _)
  have hmA' (k : Mom d) : StronglyMeasurable (A' k) := by
    have hh := (continuousMultilinearCurryFin0 ℝ (Mom d) ℂ).continuous.comp_stronglyMeasurable
      (hm' 0 (by omega) k)
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply] using hh
  have hnorm (k : Mom d) (u : U × α) : ‖A' k u‖ ≤ v' u := by
    have hh := hb' 0 (by omega) k u
    simp only [norm_iteratedFDeriv_zero] at hh
    exact (le_mul_of_one_le_left (norm_nonneg _)
      (one_le_pow₀ (one_le_momentumBracket k))).trans hh
  have hjoint (k : Mom d) := integrable_amplitude_mul_family_of_uniformL1 (μ.prod F.μ)
    (A' k) (hmA' k) (hv'.mono' (hmA' k).aestronglyMeasurable (ae_of_all _ (hnorm k)))
    K hK hiK hH hphys
  have hfull := mixedFourierNorm_spectralMixture_le (N := N) (M := M) (μ.prod F.μ) θ A' v' K
    (fun u => by
      simpa only [smul_eq_mul] using (hA u.1).const_smul (F.amplitude u.2)) (fun j hj k => (hm' j hj k).aestronglyMeasurable)
    hv' hvm' hvn' hb' hK hiK hjoint hH hphys
  apply hfull.trans
  calc
    _ ≤ ∫⁻ u, ENNReal.ofReal (v' u) * Z ∂μ.prod F.μ :=
      lintegral_mono (fun u => mul_le_mul' le_rfl (hdecay u))
    _ = (∫⁻ u, ENNReal.ofReal (v' u) ∂μ.prod F.μ) * Z :=
      lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hvm')
    _ = _ := by
      congr 1
      simp only [v', ENNReal.ofReal_mul (hvn _)]
      calc
        _ = (∫⁻ u, ENNReal.ofReal (v u) ∂μ) *
            (∫⁻ a, ENNReal.ofReal ‖F.amplitude a‖ ∂F.μ) :=
          lintegral_prod_mul (μ := μ) (ν := F.μ)
            (f := fun u => ENNReal.ofReal (v u)) (g := fun a => ENNReal.ofReal ‖F.amplitude a‖)
            (ENNReal.measurable_ofReal.comp hvm).aemeasurable
            (ENNReal.measurable_ofReal.comp hamp.norm).aemeasurable
        _ = _ := by
          simp only [SpatialMeasure.mass, ofReal_norm]
          rw [ofReal_integral_norm_eq_lintegral_enorm F.amplitude_integrable]

end WaveTurbulence.Flower.IncTop