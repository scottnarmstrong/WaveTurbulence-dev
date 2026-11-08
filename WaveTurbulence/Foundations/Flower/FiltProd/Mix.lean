/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltProd.Sel
public import WaveTurbulence.Foundations.Incoh.NormalizedLinkMixture

/-! # D5b-2 FILT-PROD: selected-link mixtures (twins of `LinkMixtureMass`, `ProductLinkMixture`,
`NormalizedLinkMixture`). Link `i` carries `φ i`; main's `productLinkMixtureMeasure` is reused. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltProd
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc

/-! ### `LinkMixtureMass` -/

theorem lintegral_linkMixtureFactorFilt_selected {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) :
    (∫⁻ z, ‖linkMixtureFactorFilt L γ δ Q φ true z‖ₑ ∂linkMixtureMeasure d true) =
      ENNReal.ofReal (∑' p, ‖filtLinkPhaseCoefficient L Q φ p‖) := by
  change (∫⁻ z : LinkMixturePoint d,
    ‖(linkBox Q).indicator (fun _ => filtLinkPhaseCoefficient L Q φ z.1) z.2‖ₑ
      ∂(Measure.count.prod volume)) = _
  have hm := (stronglyMeasurable_linkMixtureFactorFilt hL γ δ Q φ true).measurable.enorm
  change Measurable (fun z : LinkMixturePoint d =>
    ‖(linkBox Q).indicator (fun _ => filtLinkPhaseCoefficient L Q φ z.1) z.2‖ₑ) at hm
  rw [lintegral_prod _ hm.aemeasurable]
  have he (p : (Fin d → ℤ) × (Fin d → ℤ)) :
      (∫⁻ t, ‖(linkBox Q).indicator (fun _ => filtLinkPhaseCoefficient L Q φ p) t‖ₑ) =
        ‖filtLinkPhaseCoefficient L Q φ p‖ₑ := by
    simp_rw [enorm_indicator_eq_indicator_enorm]
    rw [lintegral_indicator (s := linkBox Q) measurableSet_Icc, lintegral_const, Measure.restrict_apply_univ,
      volume_linkBox, mul_one]
  simp_rw [he]
  rw [lintegral_count]
  simp_rw [← ofReal_norm]
  have hfin := finite_support_filtLinkPhaseCoefficient hL Q φ
  have hsum : Summable (fun p => ‖filtLinkPhaseCoefficient L Q φ p‖) := by
    refine summable_of_ne_finset_zero (s := hfin.toFinset) (fun p hp => ?_)
    rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hp
    rw [hp, norm_zero]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsum).symm

theorem lintegral_linkMixtureFactorFilt_unselected {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (φ : ℝ → ℂ) :
    (∫⁻ z, ‖linkMixtureFactorFilt L γ δ Q φ false z‖ₑ ∂linkMixtureMeasure d false) =
      filtLayerLinkMass L (δ * L ^ (2 * γ)) Q φ := by
  change (∫⁻ z : LinkMixturePoint d, ‖(linkBox Q).indicator (filtLinkTimeFactor L γ δ Q φ) z.2‖ₑ
    ∂((Measure.dirac 0).prod volume)) = _
  have hm := (stronglyMeasurable_linkMixtureFactorFilt hL γ δ Q φ false).measurable.enorm
  change Measurable (fun z : LinkMixturePoint d =>
    ‖(linkBox Q).indicator (filtLinkTimeFactor L γ δ Q φ) z.2‖ₑ) at hm
  rw [lintegral_prod _ hm.aemeasurable]
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [lintegral_indicator (s := linkBox Q) measurableSet_Icc]
  simp only [lintegral_const, Measure.dirac_apply_of_mem (mem_univ _), mul_one]
  rw [filtLayerLinkMass_eq]

theorem lintegral_linkMixtureFactorFilt_le {d n : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ i u, ‖φ i u‖ ≤ K) (J : Finset (Fin n)) (i : Fin n) :
    (∫⁻ z, ‖linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ J)) z‖ₑ
      ∂linkMixtureMeasure d (decide (i ∈ J))) ≤ replacedLinkMassFilt K L γ δ Q φ J i := by
  classical
  by_cases hi : i ∈ J
  · simp only [hi, decide_true, replacedLinkMassFilt, ite_true]
    rw [lintegral_linkMixtureFactorFilt_selected (zero_lt_one.trans_le hL)]
    exact ENNReal.ofReal_le_ofReal (tsum_norm_filtLinkPhaseCoefficient_le hL (Q i) (φ i) hK (hB i))
  · simp only [hi, decide_false, replacedLinkMassFilt, ite_false]
    exact (lintegral_linkMixtureFactorFilt_unselected (zero_lt_one.trans_le hL) γ δ (Q i) (φ i)).le

/-! ### `ProductLinkMixture` -/

/-- Twin of `productLinkMixtureAmplitude`. -/
def productLinkMixtureAmplitudeFilt {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) (J : Finset (Fin n)) (S : Set (Fin n → LinkMixturePoint d))
    (z : Fin n → LinkMixturePoint d) : ℂ :=
  S.indicator (fun z => ∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ J)) (z i)) z

theorem stronglyMeasurable_productLinkMixtureAmplitudeFilt {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    StronglyMeasurable (productLinkMixtureAmplitudeFilt L γ δ Q φ J S) := by
  apply StronglyMeasurable.indicator _ hS
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_prod
  intro i _
  exact (stronglyMeasurable_linkMixtureFactorFilt hL γ δ (Q i) (φ i) _).measurable.comp
    (measurable_pi_apply i)

theorem integrable_productLinkMixtureAmplitudeFilt {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    Integrable (productLinkMixtureAmplitudeFilt L γ δ Q φ J S) (productLinkMixtureMeasure d n J) := by
  exact (Integrable.fintype_prod_dep
    (fun i => integrable_linkMixtureFactorFilt hL γ δ (Q i) (φ i) (decide (i ∈ J)))).indicator hS

theorem lintegral_productLinkMixtureAmplitudeFilt_le {d n : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ i u, ‖φ i u‖ ≤ K) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    (∫⁻ z, ‖productLinkMixtureAmplitudeFilt L γ δ Q φ J S z‖ₑ ∂productLinkMixtureMeasure d n J) ≤
      ∏ i, replacedLinkMassFilt K L γ δ Q φ J i := by
  unfold productLinkMixtureAmplitudeFilt productLinkMixtureMeasure
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [lintegral_indicator hS]
  have hf (i : Fin n) : IntegrableOn (linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ J))) univ
      (linkMixtureMeasure d (decide (i ∈ J))) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      integrable_linkMixtureFactorFilt (zero_lt_one.trans_le hL) γ δ (Q i) (φ i) (decide (i ∈ J))
  apply (lintegral_pi_product_enorm_le (μ := fun i => linkMixtureMeasure d (decide (i ∈ J)))
    (B := fun _ => univ) (fun z _ => by simp) hf).trans
  apply Finset.prod_le_prod
  intro i _
  simpa only [Measure.restrict_univ] using lintegral_linkMixtureFactorFilt_le hL γ δ Q φ hK hB J i

/-! ### `NormalizedLinkMixture` -/

/-- Twin of `normalizedLinkMixtureAmplitude`. -/
def normalizedLinkMixtureAmplitudeFilt {d n : ℕ} (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (φ : Fin n → ℝ → ℂ) (J : Finset (Fin n)) (S : Set (Fin n → LinkMixturePoint d))
    (z : Fin n → LinkMixturePoint d) : ℂ :=
  (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ) *
    productLinkMixtureAmplitudeFilt L γ δ Q φ J S z

theorem stronglyMeasurable_normalizedLinkMixtureAmplitudeFilt {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    StronglyMeasurable (normalizedLinkMixtureAmplitudeFilt L γ δ Q φ J S) :=
  (stronglyMeasurable_productLinkMixtureAmplitudeFilt hL γ δ Q φ J hS).const_mul _

theorem integrable_normalizedLinkMixtureAmplitudeFilt {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    Integrable (normalizedLinkMixtureAmplitudeFilt L γ δ Q φ J S) (productLinkMixtureMeasure d n J) :=
  (integrable_productLinkMixtureAmplitudeFilt hL γ δ Q φ J hS).const_mul _

theorem lintegral_normalizedLinkMixtureAmplitudeFilt_le {d n : ℕ} {L δ : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (γ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ) {K : ℝ}
    (hK : 0 ≤ K) (hB : ∀ i u, ‖φ i u‖ ≤ K) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    (∫⁻ z, ‖normalizedLinkMixtureAmplitudeFilt L γ δ Q φ J S z‖ₑ ∂productLinkMixtureMeasure d n J) ≤
      normalizedReplacedLinkMassFilt K L γ δ Q φ J := by
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  have hnorm : ‖((((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) : ℂ))‖ₑ =
      ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  simp_rw [normalizedLinkMixtureAmplitudeFilt, enorm_mul, hnorm]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' le_rfl (lintegral_productLinkMixtureAmplitudeFilt_le hL γ δ Q φ hK hB J hS)

theorem exists_normalizedLinkMixtureAmplitudeFilt_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ k : ℕ, ∀ J : Finset (Fin n), J.card ≤ k →
        ∀ S : Set (Fin n → LinkMixturePoint d), MeasurableSet S →
        (∫⁻ z, ‖normalizedLinkMixtureAmplitudeFilt L γ δ Q φ J S z‖ₑ ∂productLinkMixtureMeasure d n J) ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) * L ^ ((d : ℝ) * k)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_normalizedReplacedFiltLinkMass_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan K hK φ hφ k J hJ S hS
  have hB : ∀ i u, ‖φ i u‖ ≤ K := fun i u =>
    PresentedMult.norm_le (hφ i) (zero_lt_one.trans_le (hL₀.trans hL)).le hK u
  exact (lintegral_normalizedLinkMixtureAmplitudeFilt_le (hL₀.trans hL) hδ γ Q φ hK hB J hS).trans
    (hb L hL n Q hspan K hK φ hφ k J hJ)

end WaveTurbulence.Flower.FiltProd
