/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltProd.Cumul
public import WaveTurbulence.Foundations.Flower.FiltProd.Expand
public import WaveTurbulence.Foundations.Incoh.TreeCommonExtension

/-! # D5b-2 FILT-PROD: tree causal mixtures (twins of `TreeCausalMixtureIntegral`, `TreeCausalMixtureSource`, `TreeNormalizedMixtureSource`, `TreeCommonExtension`)

`TreeClockFibers.fooFilt T φ …` takes the link multipliers `φ : Fin n → ℝ → ℂ` right after the fibers `T`; the
family versions take `φ : Mom d → Fin n → ℝ → ℂ`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltProd
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc
/-- The literal integrand of the positive-norm causal mixture. -/
def TreeClockFibers.causalMixtureIntegrandFilt {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (φ : Fin n → ℝ → ℂ) (L γ δ : ℝ) (χ : ℝ → ℝ) (t : Fin 2 → ℝ)
    (z : Fin n → LinkMixturePoint d) : ℂ :=
  productLinkMixtureAmplitudeFilt L γ δ Q φ T.selection.coordinates.rootLinks T.mixtureDomain z *
    universalCausalBoxKernel m χ t (T.mixtureParameters L γ δ z)

/-- The mixture depends on dummy selected times only through their layer-box factors. -/
theorem TreeClockFibers.causalMixtureIntegrand_eqFilt {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (φ : Fin n → ℝ → ℂ) (L γ δ : ℝ) (χ : ℝ → ℝ) (t : Fin 2 → ℝ)
    (z : Fin n → LinkMixturePoint d) :
    TreeClockFibers.causalMixtureIntegrandFilt T φ L γ δ χ t z =
      (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ T.selection.coordinates.rootLinks)) (z i)) *
        T.remainingCausalKernel L γ δ χ t (fun i => (z i).1)
          (T.selection.coordinates.equiv (fun i => (z i).2)).2 := by
  by_cases hz : (T.selection.coordinates.equiv (fun i => (z i).2)).2 ∈ T.remainingDomain <;>
    simp [TreeClockFibers.causalMixtureIntegrandFilt, TreeClockFibers.remainingCausalKernel,
      productLinkMixtureAmplitudeFilt, TreeClockFibers.mixtureDomain, TreeClockFibers.mixtureParameters, hz]

/-- Actual amplitude mass and the common kernel bound prove pointwise mixture integrability. -/
theorem TreeClockFibers.integrable_causalMixtureIntegrandFilt {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (φ : Fin n → ℝ → ℂ) {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {χ : ℝ → ℝ}
    (hmχ : Measurable χ) (hc : Fourier.CutoffControl χ) (t : Fin 2 → ℝ) :
    Integrable (TreeClockFibers.causalMixtureIntegrandFilt T φ L γ δ χ t)
      (productLinkMixtureMeasure d n T.selection.coordinates.rootLinks) := by
  have hmK : StronglyMeasurable (fun z : Fin n → LinkMixturePoint d =>
      universalCausalBoxKernel m χ t (T.mixtureParameters L γ δ z)) :=
    (stronglyMeasurable_universalCausalBoxKernel m hmχ).comp_measurable
      (g := fun z => (t, T.mixtureParameters L γ δ z))
      (measurable_const.prodMk (T.measurable_mixtureParameters L γ δ))
  exact (integrable_productLinkMixtureAmplitudeFilt hL γ δ Q φ T.selection.coordinates.rootLinks
    T.measurableSet_mixtureDomain).mul_bdd hmK.aestronglyMeasurable
      (c := rectangleKernelDominator hc (m + 2) t) (Filter.Eventually.of_forall (fun z =>
        norm_causalBoxKernel_le m hc _ _ _ (T.mixtureParameters L γ δ z).lower_le_upper t))

/-- The actual causal mixture equals its phase/remaining-clock integral. -/
theorem TreeClockFibers.integral_causalMixture_eq_remainingFilt {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (φ : Fin n → ℝ → ℂ) {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {χ : ℝ → ℝ}
    (hmχ : Measurable χ) (hc : Fourier.CutoffControl χ) (t : Fin 2 → ℝ) :
    (∫ z, TreeClockFibers.causalMixtureIntegrandFilt T φ L γ δ χ t z
      ∂productLinkMixtureMeasure d n T.selection.coordinates.rootLinks) =
      ∫ p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)),
        (∫ u : Fin T.selection.coordinates.restCount → ℝ,
          (T.selection.coordinates.restBox Q).indicator
            (fun _ => RootCoordinates.remainingMixtureFactorFilt T.selection.coordinates L γ δ Q φ p u) u *
              T.remainingCausalKernel L γ δ χ t p u)
        ∂Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ T.selection.coordinates.rootLinks))) := by
  have hi := (TreeClockFibers.integrable_causalMixtureIntegrandFilt T φ hL γ δ hmχ hc t).congr
    (Filter.Eventually.of_forall (TreeClockFibers.causalMixtureIntegrand_eqFilt T φ L γ δ χ t))
  simp_rw [TreeClockFibers.causalMixtureIntegrand_eqFilt T φ L γ δ χ t]
  exact RootCoordinates.integral_selectedPhaseMixtureFilt T.selection.coordinates L γ δ Q φ
    (T.remainingCausalKernel L γ δ χ t) hi



/-- The actual positive-norm mixture agrees with the source on forward external clocks. -/
theorem TreeClockFibers.causalMixture_eq_sourceFilt {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (φ : Fin n → ℝ → ℂ) (R : RootCoordinates n)
    (hfirst : R.rootVertex 0 = T.selection.coordinates.rootVertex 0)
    (hlast : R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (m + 1)))
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {χ : ℝ → ℝ} (hmχ : Measurable χ)
    (hc : Fourier.CutoffControl χ)
    (hχ : ∀ v ∈ T.selection.coordinates.rootBox Q, ∀ j, χ (v j) = 1)
    {t : Fin 2 → ℝ} (hst : t 1 ≤ t 0) :
    (∫ z, productLinkMixtureAmplitudeFilt L γ δ Q φ T.selection.coordinates.rootLinks T.mixtureDomain z *
      universalCausalBoxKernel m χ t (T.mixtureParameters L γ δ z)
      ∂productLinkMixtureMeasure d n T.selection.coordinates.rootLinks) =
      (χ (t 0) : ℂ) * (χ (t 1) : ℂ) *
        ∫ w in T.timeDomain ∩ R.causalRootCut t, ∏ i, filtLinkTimeFactor L γ δ (Q i) (φ i) (w i) := by
  change (∫ z, TreeClockFibers.causalMixtureIntegrandFilt T φ L γ δ χ t z
    ∂productLinkMixtureMeasure d n T.selection.coordinates.rootLinks) = _
  rw [TreeClockFibers.integral_causalMixture_eq_remainingFilt T φ hL γ δ hmχ hc t,
    TreeClockFibers.integral_source_eq_phaseFibersFilt T φ R hfirst hlast hL γ δ t, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ T.remainingDomain
  · have hχu (v : Fin (m + 2) → ℝ) (hv : ∀ j, T.lower u j < v j ∧ v j ≤ T.upper u j) :
        ∀ j, χ (v j) = 1 := hχ v (T.interval_mem_box u hu v hv)
    dsimp only [TreeClockFibers.remainingCausalKernel]
    rw [indicator_of_mem hu, indicator_of_mem hu]
    change _ * causalBoxKernel m χ
      (T.selection.phase (fun i => linkTemporalFrequency L γ δ (Q i) (p i)))
      (T.lower u) (T.upper u) t = _
    rw [causalBoxKernel_eq_sourceIntegral m χ _ _ _ hχu hst]
    ac_rfl
  · simp [TreeClockFibers.remainingCausalKernel, hu]



/-- The literal normalized phase kernel for the structural tree clock fibers. -/
def TreeClockFibers.causalPhaseKernelFilt {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (φ : Fin n → ℝ → ℂ) (χ : ℝ → ℝ) (L γ δ : ℝ) (t : Fin 2 → ℝ) : ℂ :=
  ∫ z, normalizedLinkMixtureAmplitudeFilt L γ δ Q φ T.selection.coordinates.rootLinks T.mixtureDomain z *
    universalCausalBoxKernel m χ t (T.mixtureParameters L γ δ z)
    ∂productLinkMixtureMeasure d n T.selection.coordinates.rootLinks

/-- Exact source agreement with the full source coupling and both external cutoffs. -/
theorem TreeClockFibers.causalPhaseKernel_eq_sourceFilt {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (φ : Fin n → ℝ → ℂ) (R : RootCoordinates n)
    (hfirst : R.rootVertex 0 = T.selection.coordinates.rootVertex 0)
    (hlast : R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (m + 1)))
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {χ : ℝ → ℝ} (hmχ : Measurable χ)
    (hc : Fourier.CutoffControl χ)
    (hχ : ∀ v ∈ T.selection.coordinates.rootBox Q, ∀ j, χ (v j) = 1)
    {t : Fin 2 → ℝ} (hst : t 1 ≤ t 0) :
    TreeClockFibers.causalPhaseKernelFilt T φ χ L γ δ t =
      (χ (t 0) : ℂ) * (χ (t 1) : ℂ) * RootCoordinates.causalKernelFilt R L γ δ Q φ T.timeDomain t := by
  unfold TreeClockFibers.causalPhaseKernelFilt
  simp_rw [normalizedLinkMixtureAmplitudeFilt, mul_assoc]
  rw [integral_const_mul, TreeClockFibers.causalMixture_eq_sourceFilt T φ R hfirst hlast hL γ δ hmχ hc hχ hst]
  unfold RootCoordinates.causalKernelFilt normalizedLinkIntegralFilt
  ac_rfl

/-- All literal normalized causal phase mixtures vanish at reversed external clocks. -/
theorem TreeClockFibers.causalPhaseKernel_eq_zero_of_reverseFilt {d n m : ℕ}
    {Q : Fin n → LayerLink d} (T : TreeClockFibers m Q) (φ : Fin n → ℝ → ℂ) (χ : ℝ → ℝ) (L γ δ : ℝ)
    {t : Fin 2 → ℝ} (ht : t 0 ≤ t 1) : TreeClockFibers.causalPhaseKernelFilt T φ χ L γ δ t = 0 := by
  unfold TreeClockFibers.causalPhaseKernelFilt universalCausalBoxKernel
  simp_rw [causalBoxKernel_eq_zero_of_reverse χ _ _ _ ht, mul_zero]
  exact integral_zero _ _



/-- TARGET (incohproof26) and (incohproof28) estimate one actual extension globally. -/
theorem treeCausalExtension_eq_phaseKernel {d n m : ℕ} (R : RootCoordinates n)
    (Q : Mom d → Fin n → LayerLink d) (T : ∀ k, TreeClockFibers m (Q k)) (φ : Mom d → Fin n → ℝ → ℂ)
    (hfirst : ∀ k, R.rootVertex 0 = (T k).selection.coordinates.rootVertex 0)
    (hlast : ∀ k, R.rootVertex 1 = (T k).selection.coordinates.rootVertex (Fin.last (m + 1)))
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {χ : ℝ → ℝ} (hmχ : Measurable χ)
    (hc : Fourier.CutoffControl χ)
    (hχroot : ∀ k v, v ∈ R.rootBox (Q k) → ∀ j, χ (v j) = 1)
    (hχselected : ∀ k v, v ∈ (T k).selection.coordinates.rootBox (Q k) → ∀ j, χ (v j) = 1) :
    RootCoordinates.treeCausalExtensionFilt R χ L γ δ Q φ (fun k => (T k).timeDomain) =
      fun t k => TreeClockFibers.causalPhaseKernelFilt (T k) (φ k) χ L γ δ t := by
  funext t k
  by_cases ht : t 1 ≤ t 0
  · rw [RootCoordinates.treeCausalExtension_eq_weighted_sourceFilt R hL γ δ Q φ (fun k => (T k).timeDomain) k
      (T k).measurableSet_timeDomain (T k).timeDomain_subset_linkBoxes (hχroot k) ht]
    exact (TreeClockFibers.causalPhaseKernel_eq_sourceFilt (T k) (φ k) R (hfirst k) (hlast k) hL γ δ hmχ hc (hχselected k) ht).symm
  · rw [RootCoordinates.treeCausalExtension_eq_zero_of_reverseFilt R χ L γ δ Q φ (fun k => (T k).timeDomain) k
      ((T k).root_order R (hfirst k) (hlast k)) (le_of_not_ge ht),
      TreeClockFibers.causalPhaseKernel_eq_zero_of_reverseFilt (T k) (φ k) χ L γ δ (le_of_not_ge ht)]


end WaveTurbulence.Flower.FiltProd
