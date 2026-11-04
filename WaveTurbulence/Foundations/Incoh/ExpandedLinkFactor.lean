/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.PhaseTimeSplit

/-!
# Literal selected-link factors with their temporal phases

The expanded integrand is integrable for the actual counting/Dirac
mixture measure. Its phase integral recovers the original link factor.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Restore the temporal exponential to a selected link's mixture coefficient. -/
@[expose] def linkMixturePhase {d : ℕ} (L γ δ : ℝ) (Q : LayerLink d) (selected : Bool)
    (z : LinkMixturePoint d) : ℂ :=
  if selected then Complex.exp ((linkTemporalFrequency L γ δ Q z.1 * (z.2 0 - z.2 1) : ℝ) *
    Complex.I) else 1

/-- A literal temporal exponential has unit modulus even at unused phase coordinates. -/
theorem norm_linkMixturePhase {d : ℕ} (L γ δ : ℝ) (Q : LayerLink d)
    (selected : Bool) (z : LinkMixturePoint d) : ‖linkMixturePhase L γ δ Q selected z‖ = 1 := by
  cases selected <;> simp [linkMixturePhase, Complex.norm_exp]

/-- Temporal phases are jointly measurable in lattice and clock coordinates. -/
theorem measurable_linkMixturePhase {d : ℕ} (L γ δ : ℝ) (Q : LayerLink d)
    (selected : Bool) : Measurable (linkMixturePhase L γ δ Q selected) := by
  cases selected
  · exact measurable_const
  · have hf : Measurable (linkTemporalFrequency L γ δ Q) := measurable_of_countable _
    have hp : Measurable (fun z : LinkMixturePoint d => linkTemporalFrequency L γ δ Q z.1) :=
      hf.comp measurable_fst
    exact Complex.continuous_exp.measurable.comp
      ((Complex.continuous_ofReal.measurable.comp
        (hp.mul (((measurable_pi_apply 0).comp measurable_snd).sub
          ((measurable_pi_apply 1).comp measurable_snd)))).mul measurable_const)

/-- Phase integration recovers the actual factor with its literal layer box. -/
theorem integral_expandedLinkFactor {d : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ)
    (Q : LayerLink d) (selected : Bool) (t : Fin 2 → ℝ) :
    (∫ p, linkMixtureFactor L γ δ Q selected (p, t) *
      linkMixturePhase L γ δ Q selected (p, t) ∂phaseCoordinateMeasure d selected) =
      (linkBox Q).indicator (linkTimeFactor L γ δ Q) t := by
  by_cases ht : t ∈ linkBox Q
  · simp only [linkMixtureFactor, indicator_of_mem ht]
    cases selected
    · change (∫ _p, linkTimeFactor L γ δ Q t * 1 ∂Measure.dirac 0) = _
      simp
    · change (∫ p, phaseCoordinateTerm L γ δ Q true t p ∂phaseCoordinateMeasure d true) = _
      rw [integral_phaseCoordinateTerm hL γ δ Q true t]
      simp
  · simp only [linkMixtureFactor, indicator_of_notMem ht, zero_mul, integral_zero]

/-- Restoring all selected temporal phases preserves actual mixture integrability. -/
theorem integrable_expandedLinkMixture {d n : ℕ} {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (Q : Fin n → LayerLink d) (J : Finset (Fin n))
    {S : Set (Fin n → LinkMixturePoint d)} (hS : MeasurableSet S) :
    Integrable (fun z => productLinkMixtureAmplitude L γ δ Q J S z *
      ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (z i))
      (productLinkMixtureMeasure d n J) := by
  have hm : Measurable (fun z : Fin n → LinkMixturePoint d =>
      ∏ i, linkMixturePhase L γ δ (Q i) (decide (i ∈ J)) (z i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (measurable_linkMixturePhase L γ δ (Q i) _).comp (measurable_pi_apply i)
  apply (integrable_productLinkMixtureAmplitude hL γ δ Q J hS).mul_bdd
    hm.stronglyMeasurable.aestronglyMeasurable (c := 1)
  exact Filter.Eventually.of_forall (fun z => by simp [norm_prod, norm_linkMixturePhase])

end WaveTurbulence.Incoh
