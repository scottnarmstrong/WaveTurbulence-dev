/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.ProductMixture

/-! Ported by source from C2-B-TOP `Cut2BReg.ProductRootMixture` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Product Fourier measures and the tree's locally finite root partition -/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open Cut2A

/-- Conditional full-derivative transport. The supremum over the Fourier character and
spectral variables remains inside the common time-frequency integral. -/
theorem mixedFourierNorm_productRootMixture_le {r d N : ℕ} {U V α : Type*}
    [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace α]
    (μ : Measure U) [SFinite μ] (F : SpatialMeasure V α) (hamp : Measurable F.amplitude)
    (θ : ℝ) (B : (Fin d → ℤ) → Mom d → U → ℂ) (v : (Fin d → ℤ) → U → ℝ)
    (hz : ∀ q k u, treeRootCutoffSpatial q k = 0 → B q k u = 0)
    (hB : ∀ q u, ContDiff ℝ N (fun k => B q k u))
    (hm : ∀ q j, j ≤ N → ∀ k, StronglyMeasurable
      (fun u => iteratedFDeriv ℝ j (fun k => B q k u) k))
    (hv : ∀ q, Integrable (v q) μ) (hvm : ∀ q, Measurable (v q)) (hvn : ∀ q u, 0 ≤ v q u)
    (hb : ∀ q j, j ≤ N → ∀ k u, ‖iteratedFDeriv ℝ j (fun k => B q k u) k‖ ≤ v q u)
    {Z : ℝ≥0∞} (hmass : ∀ q, (∫⁻ u, ENNReal.ofReal (v q u) ∂μ) ≤ Z)
    (K : (Fin r → ℝ) → U × α → ℂ)
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × (U × α) => K z.1 z.2))
    (hiK : ∀ u, Integrable (fun t => K t u))
    {H : ℝ≥0∞} (hH : H < ⊤) (hphys : ∀ u, eLpNorm (fun t => K t u) 1 ≤ H) :
    Fourier.mixedFourierNorm θ N 0
      (fun t k => ∫ u, F.amplitude u.2 * rootAmplitudeSumSpatial B k u.1 * K t u ∂μ.prod F.μ) ≤
        (ENNReal.ofReal (rootLocalOverlapConstantSpatial d) * (Z * ENNReal.ofReal F.mass)) *
          Fourier.mixedFourierNorm00 θ K := by
  let B' := fun q k (u : U × α) => F.amplitude u.2 * B q k u.1
  let v' := fun q (u : U × α) => v q u.1 * ‖F.amplitude u.2‖
  have hs (q : Fin d → ℤ) (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U × α) :
      iteratedFDeriv ℝ j (fun k => B' q k u) k =
        F.amplitude u.2 • iteratedFDeriv ℝ j (fun k => B q k u.1) k :=
    iteratedFDeriv_mul_amplitude _ _ ((hB q u.1).of_le (by exact_mod_cast hj)) k
  have hm' (q : Fin d → ℤ) (j : ℕ) (hj : j ≤ N) (k : Mom d) :
      StronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun k => B' q k u) k) := by
    simp_rw [hs q j hj k]
    exact (hamp.comp measurable_snd).stronglyMeasurable.smul ((hm q j hj k).comp_measurable measurable_fst)
  have hv' (q : Fin d → ℤ) : Integrable (v' q) (μ.prod F.μ) := (hv q).mul_prod F.amplitude_integrable.norm
  have hvm' (q : Fin d → ℤ) : Measurable (v' q) :=
    ((hvm q).comp measurable_fst).mul (hamp.norm.comp measurable_snd)
  have hvn' (q : Fin d → ℤ) (u : U × α) : 0 ≤ v' q u := mul_nonneg (hvn _ _) (norm_nonneg _)
  have hb' (q : Fin d → ℤ) (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U × α) :
      ‖iteratedFDeriv ℝ j (fun k => B' q k u) k‖ ≤ v' q u := by
    rw [hs q j hj k u, norm_smul]
    exact (mul_le_mul_of_nonneg_left (hb q j hj k u.1) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hmz (q : Fin d → ℤ) : ∫⁻ u, ENNReal.ofReal (v' q u) ∂μ.prod F.μ ≤ Z * ENNReal.ofReal F.mass := by
    simp only [v', ENNReal.ofReal_mul (hvn _ _)]
    have he := lintegral_prod_mul (μ := μ) (ν := F.μ)
      (f := fun u => ENNReal.ofReal (v q u)) (g := fun a => ENNReal.ofReal ‖F.amplitude a‖)
      (ENNReal.measurable_ofReal.comp (hvm q)).aemeasurable
      (ENNReal.measurable_ofReal.comp hamp.norm).aemeasurable
    rw [he]
    simp only [ofReal_norm]
    rw [← ofReal_integral_norm_eq_lintegral_enorm F.amplitude_integrable]
    exact mul_le_mul' (hmass q) le_rfl
  have heq (t : Fin r → ℝ) (k : Mom d) :
      (∫ u, F.amplitude u.2 * rootAmplitudeSumSpatial B k u.1 * K t u ∂μ.prod F.μ) =
        ∫ u, rootAmplitudeSumSpatial B' k u * K t u ∂μ.prod F.μ := by
    apply integral_congr_ae
    apply ae_of_all
    intro u
    simp only [rootAmplitudeSumSpatial, B', tsum_mul_left]
  simp_rw [heq]
  exact mixedFourierNorm_rootAmplitudeMixture_leSpatial (N := N) (μ.prod F.μ) θ B' v'
    (fun q k u hq => by dsimp only [B']; rw [hz q k u.1 hq, mul_zero])
    (fun q u => by simpa only [smul_eq_mul] using (hB q u.1).const_smul (F.amplitude u.2))
    hm' hv' hvm' hvn' hb' hmz K hK hiK hH hphys

end WaveTurbulence.Flower.IncTop