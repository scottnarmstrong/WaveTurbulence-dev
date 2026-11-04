/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.ExpandedLinkFactor

/-!
# Integrability at every fixed lattice-phase array

Literal layer cutoffs make the time factors integrable before any phase
integration. Unit temporal exponentials preserve this integrability.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Fixing any lattice phase leaves an integrable literal time factor. -/
theorem integrable_linkMixtureFactor_clock {d : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : LayerLink d) (selected : Bool)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    Integrable (fun t : Fin 2 → ℝ => linkMixtureFactor L γ δ Q selected (p, t)) := by
  cases selected
  · exact (integrableOn_linkTimeFactor hL γ δ Q).integrable_indicator
      (show MeasurableSet (linkBox Q) from measurableSet_Icc)
  · exact (show IntegrableOn (fun _ : Fin 2 → ℝ => linkPhaseCoefficient L Q p) (linkBox Q) from
      continuous_const.integrableOn_Icc).integrable_indicator
        (show MeasurableSet (linkBox Q) from measurableSet_Icc)

/-- Any source-domain restriction of the literal expanded time integrand is integrable. -/
theorem integrable_expandedLinkClockArray {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (J : Finset (Fin n))
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)))
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : MeasurableSet I) :
    Integrable (I.indicator (fun t : Fin n → Fin 2 → ℝ =>
      (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ J)) (p i, t i)) *
        ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (p i, t i))) := by
  have hi : Integrable (fun t : Fin n → Fin 2 → ℝ =>
      ∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ J)) (p i, t i)) :=
    Integrable.fintype_prod_dep (fun i => integrable_linkMixtureFactor_clock hL γ δ (Q i) _ (p i))
  have hm : Measurable (fun t : Fin n → Fin 2 → ℝ =>
      ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (p i, t i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (measurable_linkMixturePhase L γ δ (Q i) _).comp
      (measurable_const.prodMk (measurable_pi_apply i))
  apply (hi.mul_bdd hm.stronglyMeasurable.aestronglyMeasurable (c := 1) ?_).indicator hI
  exact Filter.Eventually.of_forall (fun t => by simp [norm_prod, norm_linkMixturePhase])

end WaveTurbulence.Incoh
