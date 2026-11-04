/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeFiberParameters
public import WaveTurbulence.Foundations.Incoh.SelectedPhaseMixture
public import WaveTurbulence.Foundations.Incoh.CausalMixtureBound

/-!
# Integrable literal causal mixtures and their remaining-clock representation

All mixture and Fubini integrability obligations follow from the actual
link factors and common causal kernel bound.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- The literal remaining-clock mixture support. -/
@[expose] def TreeClockFibers.mixtureDomain {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) : Set (Fin n → LinkMixturePoint d) :=
  (fun z => (T.selection.coordinates.equiv (fun i => (z i).2)).2) ⁻¹' T.remainingDomain

/-- The support is measurable in the original mixture coordinates. -/
theorem TreeClockFibers.measurableSet_mixtureDomain {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) : MeasurableSet T.mixtureDomain :=
  T.measurable_remainingDomain.preimage (measurable_snd.comp
    (T.selection.coordinates.equiv.measurable.comp
      (Measurable.of_eval (fun i => measurable_snd.comp (measurable_pi_apply i)))))

/-- The actual remaining-clock causal kernel, including its source support. -/
@[expose] def TreeClockFibers.remainingCausalKernel {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (L γ δ : ℝ) (χ : ℝ → ℝ) (t : Fin 2 → ℝ)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)))
    (u : Fin T.selection.coordinates.restCount → ℝ) : ℂ :=
  T.remainingDomain.indicator (fun u => universalCausalBoxKernel m χ t (T.boxParameters L γ δ p u)) u

/-- The literal integrand of the positive-norm causal mixture. -/
@[expose] def TreeClockFibers.causalMixtureIntegrand {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (L γ δ : ℝ) (χ : ℝ → ℝ) (t : Fin 2 → ℝ)
    (z : Fin n → LinkMixturePoint d) : ℂ :=
  productLinkMixtureAmplitude L γ δ Q T.selection.coordinates.rootLinks T.mixtureDomain z *
    universalCausalBoxKernel m χ t (T.mixtureParameters L γ δ z)

/-- The mixture depends on dummy selected times only through their layer-box factors. -/
theorem TreeClockFibers.causalMixtureIntegrand_eq {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) (L γ δ : ℝ) (χ : ℝ → ℝ) (t : Fin 2 → ℝ)
    (z : Fin n → LinkMixturePoint d) :
    T.causalMixtureIntegrand L γ δ χ t z =
      (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ T.selection.coordinates.rootLinks)) (z i)) *
        T.remainingCausalKernel L γ δ χ t (fun i => (z i).1)
          (T.selection.coordinates.equiv (fun i => (z i).2)).2 := by
  by_cases hz : (T.selection.coordinates.equiv (fun i => (z i).2)).2 ∈ T.remainingDomain <;>
    simp [causalMixtureIntegrand, remainingCausalKernel, productLinkMixtureAmplitude,
      mixtureDomain, mixtureParameters, hz]

/-- Actual amplitude mass and the common kernel bound prove pointwise mixture integrability. -/
theorem TreeClockFibers.integrable_causalMixtureIntegrand {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {χ : ℝ → ℝ}
    (hmχ : Measurable χ) (hc : Fourier.CutoffControl χ) (t : Fin 2 → ℝ) :
    Integrable (T.causalMixtureIntegrand L γ δ χ t)
      (productLinkMixtureMeasure d n T.selection.coordinates.rootLinks) := by
  have hmK : StronglyMeasurable (fun z : Fin n → LinkMixturePoint d =>
      universalCausalBoxKernel m χ t (T.mixtureParameters L γ δ z)) :=
    (stronglyMeasurable_universalCausalBoxKernel m hmχ).comp_measurable
      (g := fun z => (t, T.mixtureParameters L γ δ z))
      (measurable_const.prodMk (T.measurable_mixtureParameters L γ δ))
  exact (integrable_productLinkMixtureAmplitude hL γ δ Q T.selection.coordinates.rootLinks
    T.measurableSet_mixtureDomain).mul_bdd hmK.aestronglyMeasurable
      (c := rectangleKernelDominator hc (m + 2) t) (Filter.Eventually.of_forall (fun z =>
        norm_causalBoxKernel_le m hc _ _ _ (T.mixtureParameters L γ δ z).lower_le_upper t))

/-- The actual causal mixture equals its phase/remaining-clock integral. -/
theorem TreeClockFibers.integral_causalMixture_eq_remaining {d n m : ℕ} {Q : Fin n → LayerLink d}
    (T : TreeClockFibers m Q) {L : ℝ} (hL : 0 < L) (γ δ : ℝ) {χ : ℝ → ℝ}
    (hmχ : Measurable χ) (hc : Fourier.CutoffControl χ) (t : Fin 2 → ℝ) :
    (∫ z, T.causalMixtureIntegrand L γ δ χ t z
      ∂productLinkMixtureMeasure d n T.selection.coordinates.rootLinks) =
      ∫ p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)),
        (∫ u : Fin T.selection.coordinates.restCount → ℝ,
          (T.selection.coordinates.restBox Q).indicator
            (fun _ => T.selection.coordinates.remainingMixtureFactor L γ δ Q p u) u *
              T.remainingCausalKernel L γ δ χ t p u)
        ∂Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ T.selection.coordinates.rootLinks))) := by
  have hi := (T.integrable_causalMixtureIntegrand hL γ δ hmχ hc t).congr
    (Filter.Eventually.of_forall (T.causalMixtureIntegrand_eq L γ δ χ t))
  simp_rw [T.causalMixtureIntegrand_eq L γ δ χ t]
  exact T.selection.coordinates.integral_selectedPhaseMixture L γ δ Q
    (T.remainingCausalKernel L γ δ χ t) hi

end WaveTurbulence.Incoh
