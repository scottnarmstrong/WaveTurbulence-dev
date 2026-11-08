/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Top.RootMeasure
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.ProductMixture
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.ProductRootMixture

/-! Ported by source from C2-B-TOP `C2BTop.RootMixture` (sha256 in COPIED-SHA256SUMS); mechanical edits only.
 # Full spatial norm transport for root-modulated product Fourier measures

C2-B-REG's `mixedFourierNorm_productMixture_le` and `mixedFourierNorm_productRootMixture_le` with the
amplitude `amp a * e(⟨root a, k⟩)` of `G.at k`.  The presentation parameter is integrated together
with the source spectral variables, so the root derivatives fall on `e(⟨root a, ·⟩) * A`; by Leibniz
they cost `rootJetConstant N * (1 + ‖root a‖)^N`, and the integrated cost is `G.momentMass N`.
The jet measurability of `e(⟨root a, ·⟩) * A` is a premise; the applications prove it. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh WaveTurbulence.Cut2A

variable {d n : ℕ} {α : Type} [MeasurableSpace α]

/-- `∫ v(u) (1 + ‖root a‖)^N |amp a|` over the product measure. -/
theorem lintegral_rootEnvelope_eq {U : Type*} [MeasurableSpace U] (μ : Measure U) [SFinite μ]
    (G : RootMeasure d n α) (N : ℕ) (v : U → ℝ) (hvm : Measurable v) (hvn : ∀ u, 0 ≤ v u) :
    (∫⁻ u, ENNReal.ofReal (rootJetConstant N *
        ((1 + ‖G.root u.2‖) ^ N * ‖G.base.amplitude u.2‖) * v u.1) ∂μ.prod G.base.μ) =
      ENNReal.ofReal (rootJetConstant N) * ((∫⁻ u, ENNReal.ofReal (v u) ∂μ) * G.momentMass N) := by
  have hC := (rootJetConstant_pos N).le
  have he (u : U × α) : ENNReal.ofReal (rootJetConstant N *
      ((1 + ‖G.root u.2‖) ^ N * ‖G.base.amplitude u.2‖) * v u.1) =
      ENNReal.ofReal (rootJetConstant N) * (ENNReal.ofReal (v u.1) *
        ENNReal.ofReal ((1 + ‖G.root u.2‖) ^ N * ‖G.base.amplitude u.2‖)) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hC (by positivity)), ENNReal.ofReal_mul hC]
    ring
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [G.momentMass_eq N]
  exact lintegral_prod_mul (μ := μ) (ν := G.base.μ)
    (ENNReal.measurable_ofReal.comp hvm).aemeasurable
    (ENNReal.measurable_ofReal.comp (G.measurable_momentDensity N)).aemeasurable

/-- Couple form (weighted root derivatives, order `M`). -/
theorem mixedFourierNorm_rootProductMixture_le {r N M : ℕ} {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] (G : RootMeasure d n α)
    (θ : ℝ) (A : Mom d → U → ℂ) (v : U → ℝ) (K : (Fin r → ℝ) → U × α → ℂ)
    (hA : ∀ u, ContDiff ℝ N (fun k => A k u))
    (hm : ∀ j ≤ N, ∀ k, StronglyMeasurable (fun u : U × α =>
      iteratedFDeriv ℝ j (fun k => rootChar (G.root u.2) k * A k u.1) k))
    (hv : Integrable v μ) (hvm : Measurable v) (hvn : ∀ u, 0 ≤ v u)
    (hb : ∀ j ≤ N, ∀ k u, Fourier.momentumBracket k ^ M *
      ‖iteratedFDeriv ℝ j (fun k => A k u) k‖ ≤ v u)
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × (U × α) => K z.1 z.2))
    (hiK : ∀ u, Integrable (fun t => K t u))
    {H : ℝ≥0∞} (hH : H < ⊤) (hphys : ∀ u, eLpNorm (fun t => K t u) 1 ≤ H)
    {Z : ℝ≥0∞} (hdecay : ∀ u, Fourier.timeFourierNorm θ (fun t => K t u) ≤ Z)
    (hfin : G.momentMass N < ⊤) :
    Fourier.mixedFourierNorm θ N M
      (fun t k => ∫ u, (G.at k).amplitude u.2 * A k u.1 * K t u ∂μ.prod G.base.μ) ≤
        ENNReal.ofReal (rootJetConstant N) * ((∫⁻ u, ENNReal.ofReal (v u) ∂μ) * G.momentMass N) * Z := by
  let B := fun k (u : U × α) => rootChar (G.root u.2) k * A k u.1
  let A' := fun k (u : U × α) => G.base.amplitude u.2 * B k u
  let m := fun a : α => (1 + ‖G.root a‖) ^ N * ‖G.base.amplitude a‖
  let v' := fun u : U × α => rootJetConstant N * m u.2 * v u.1
  have hC := (rootJetConstant_pos N).le
  have hB (u : U × α) : ContDiff ℝ N (fun k => B k u) :=
    ((contDiff_momentumModulation (G.root u.2)).of_le (by exact_mod_cast le_top)).mul (hA u.1)
  have hs (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U × α) :
      iteratedFDeriv ℝ j (fun k => A' k u) k =
        G.base.amplitude u.2 • iteratedFDeriv ℝ j (fun k => B k u) k :=
    iteratedFDeriv_mul_amplitude _ _ ((hB u).of_le (by exact_mod_cast hj)) k
  have hm' (j : ℕ) (hj : j ≤ N) (k : Mom d) :
      StronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun k => A' k u) k) := by
    simp_rw [hs j hj k]
    exact (G.amplitude_measurable.comp measurable_snd).stronglyMeasurable.smul (hm j hj k)
  have hmint : Integrable m G.base.μ := G.integrable_momentDensity N hfin
  have hv' : Integrable v' (μ.prod G.base.μ) := by
    have h := hv.mul_prod hmint
    refine (h.const_mul (rootJetConstant N)).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [v']
    ring
  have hvm' : Measurable v' :=
    (measurable_const.mul ((G.measurable_momentDensity N).comp measurable_snd)).mul
      (hvm.comp measurable_fst)
  have hvn' (u : U × α) : 0 ≤ v' u := mul_nonneg (mul_nonneg hC (by positivity)) (hvn _)
  have hb' (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U × α) :
      Fourier.momentumBracket k ^ M * ‖iteratedFDeriv ℝ j (fun k => A' k u) k‖ ≤ v' u := by
    rw [hs j hj k u, norm_smul]
    have hl := norm_iteratedFDeriv_rootChar_mul_le (G.root u.2) (hA u.1) hj
      (fun i hi k => hb i hi k u.1) k
    calc
      _ = ‖G.base.amplitude u.2‖ * (Fourier.momentumBracket k ^ M *
          ‖iteratedFDeriv ℝ j (fun k => B k u) k‖) := by ring
      _ ≤ ‖G.base.amplitude u.2‖ * (rootJetConstant N * (1 + ‖G.root u.2‖) ^ N * v u.1) :=
        mul_le_mul_of_nonneg_left hl (norm_nonneg _)
      _ = v' u := by simp only [v', m]; ring
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
  have hjoint (k : Mom d) := integrable_amplitude_mul_family_of_uniformL1 (μ.prod G.base.μ)
    (A' k) (hmA' k) (hv'.mono' (hmA' k).aestronglyMeasurable (Filter.Eventually.of_forall (hnorm k)))
    K hK hiK hH hphys
  have hfull := mixedFourierNorm_spectralMixture_le (N := N) (M := M) (μ.prod G.base.μ) θ A' v' K
    (fun u => by simpa only [smul_eq_mul] using (hB u).const_smul (G.base.amplitude u.2))
    (fun j hj k => (hm' j hj k).aestronglyMeasurable)
    hv' hvm' hvn' hb' hK hiK hjoint hH hphys
  have heq : (fun t k => ∫ u, (G.at k).amplitude u.2 * A k u.1 * K t u ∂μ.prod G.base.μ) =
      fun t k => ∫ u, A' k u * K t u ∂μ.prod G.base.μ := by
    funext t k
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [A', B, RootMeasure.at_amplitude]
    ring
  rw [heq]
  apply hfull.trans
  calc
    _ ≤ ∫⁻ u, ENNReal.ofReal (v' u) * Z ∂μ.prod G.base.μ :=
      lintegral_mono (fun u => mul_le_mul' le_rfl (hdecay u))
    _ = (∫⁻ u, ENNReal.ofReal (v' u) ∂μ.prod G.base.μ) * Z :=
      lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hvm')
    _ = _ := by
      congr 1
      exact lintegral_rootEnvelope_eq μ G N v hvm hvn

/-- Tree form (finite root-cell models, no root weight). -/
theorem mixedFourierNorm_rootProductRootMixture_le {r N : ℕ} {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] (G : RootMeasure d n α)
    (θ : ℝ) (B : (Fin d → ℤ) → Mom d → U → ℂ) (v : (Fin d → ℤ) → U → ℝ)
    (hz : ∀ q k u, treeRootCutoffSpatial q k = 0 → B q k u = 0)
    (hB : ∀ q u, ContDiff ℝ N (fun k => B q k u))
    (hm : ∀ q j, j ≤ N → ∀ k, StronglyMeasurable (fun u : U × α =>
      iteratedFDeriv ℝ j (fun k => rootChar (G.root u.2) k * B q k u.1) k))
    (hv : ∀ q, Integrable (v q) μ) (hvm : ∀ q, Measurable (v q)) (hvn : ∀ q u, 0 ≤ v q u)
    (hb : ∀ q j, j ≤ N → ∀ k u, ‖iteratedFDeriv ℝ j (fun k => B q k u) k‖ ≤ v q u)
    {Z : ℝ≥0∞} (hmass : ∀ q, (∫⁻ u, ENNReal.ofReal (v q u) ∂μ) ≤ Z)
    (K : (Fin r → ℝ) → U × α → ℂ)
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × (U × α) => K z.1 z.2))
    (hiK : ∀ u, Integrable (fun t => K t u))
    {H : ℝ≥0∞} (hH : H < ⊤) (hphys : ∀ u, eLpNorm (fun t => K t u) 1 ≤ H)
    (hfin : G.momentMass N < ⊤) :
    Fourier.mixedFourierNorm θ N 0
      (fun t k => ∫ u, (G.at k).amplitude u.2 * rootAmplitudeSumSpatial B k u.1 * K t u
        ∂μ.prod G.base.μ) ≤
        (ENNReal.ofReal (rootLocalOverlapConstantSpatial d) *
          (ENNReal.ofReal (rootJetConstant N) * (Z * G.momentMass N))) *
          Fourier.mixedFourierNorm00 θ K := by
  let B' := fun q k (u : U × α) => G.base.amplitude u.2 * (rootChar (G.root u.2) k * B q k u.1)
  let m := fun a : α => (1 + ‖G.root a‖) ^ N * ‖G.base.amplitude a‖
  let v' := fun q (u : U × α) => rootJetConstant N * m u.2 * v q u.1
  have hC := (rootJetConstant_pos N).le
  have hBB (q : Fin d → ℤ) (u : U × α) : ContDiff ℝ N (fun k => rootChar (G.root u.2) k * B q k u.1) :=
    ((contDiff_momentumModulation (G.root u.2)).of_le (by exact_mod_cast le_top)).mul (hB q u.1)
  have hs (q : Fin d → ℤ) (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U × α) :
      iteratedFDeriv ℝ j (fun k => B' q k u) k =
        G.base.amplitude u.2 • iteratedFDeriv ℝ j (fun k => rootChar (G.root u.2) k * B q k u.1) k :=
    iteratedFDeriv_mul_amplitude _ _ ((hBB q u).of_le (by exact_mod_cast hj)) k
  have hm' (q : Fin d → ℤ) (j : ℕ) (hj : j ≤ N) (k : Mom d) :
      StronglyMeasurable (fun u => iteratedFDeriv ℝ j (fun k => B' q k u) k) := by
    simp_rw [hs q j hj k]
    exact (G.amplitude_measurable.comp measurable_snd).stronglyMeasurable.smul (hm q j hj k)
  have hmint : Integrable m G.base.μ := G.integrable_momentDensity N hfin
  have hv' (q : Fin d → ℤ) : Integrable (v' q) (μ.prod G.base.μ) := by
    have h := (hv q).mul_prod hmint
    refine (h.const_mul (rootJetConstant N)).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [v']
    ring
  have hvm' (q : Fin d → ℤ) : Measurable (v' q) :=
    (measurable_const.mul ((G.measurable_momentDensity N).comp measurable_snd)).mul
      ((hvm q).comp measurable_fst)
  have hvn' (q : Fin d → ℤ) (u : U × α) : 0 ≤ v' q u :=
    mul_nonneg (mul_nonneg hC (by positivity)) (hvn _ _)
  have hb' (q : Fin d → ℤ) (j : ℕ) (hj : j ≤ N) (k : Mom d) (u : U × α) :
      ‖iteratedFDeriv ℝ j (fun k => B' q k u) k‖ ≤ v' q u := by
    rw [hs q j hj k u, norm_smul]
    have hl := norm_iteratedFDeriv_rootChar_mul_le (W := 0) (G.root u.2) (hB q u.1) hj
      (fun i hi k => by simpa only [pow_zero, one_mul] using hb q i hi k u.1) k
    simp only [pow_zero, one_mul] at hl
    calc
      _ ≤ ‖G.base.amplitude u.2‖ * (rootJetConstant N * (1 + ‖G.root u.2‖) ^ N * v q u.1) :=
        mul_le_mul_of_nonneg_left hl (norm_nonneg _)
      _ = v' q u := by simp only [v', m]; ring
  have hmz (q : Fin d → ℤ) : ∫⁻ u, ENNReal.ofReal (v' q u) ∂μ.prod G.base.μ ≤
      ENNReal.ofReal (rootJetConstant N) * (Z * G.momentMass N) := by
    have he := lintegral_rootEnvelope_eq μ G N (v q) (hvm q) (hvn q)
    simp only [v', m] at he ⊢
    rw [he]
    exact mul_le_mul' le_rfl (mul_le_mul' (hmass q) le_rfl)
  have heq (t : Fin r → ℝ) (k : Mom d) :
      (∫ u, (G.at k).amplitude u.2 * rootAmplitudeSumSpatial B k u.1 * K t u ∂μ.prod G.base.μ) =
        ∫ u, rootAmplitudeSumSpatial B' k u * K t u ∂μ.prod G.base.μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [rootAmplitudeSumSpatial, B', RootMeasure.at_amplitude, tsum_mul_left]
    ring
  simp_rw [heq]
  exact mixedFourierNorm_rootAmplitudeMixture_leSpatial (N := N) (μ.prod G.base.μ) θ B' v'
    (fun q k u hq => by simp only [B']; rw [hz q k u.1 hq, mul_zero, mul_zero])
    (fun q u => by simpa only [smul_eq_mul] using (hBB q u).const_smul (G.base.amplitude u.2))
    hm' hv' hvm' hvn' hb' hmz K hK hiK hH hphys

end WaveTurbulence.Flower.IncTop