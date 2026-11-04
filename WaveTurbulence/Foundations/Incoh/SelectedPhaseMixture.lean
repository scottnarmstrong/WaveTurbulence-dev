/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SelectedMixtureIntegral
public import WaveTurbulence.Foundations.Incoh.PhaseTimeSplit

/-!
# Exact collapse of a selected-link phase mixture

The dummy selected times integrate to one. All remaining dependence is
retained, including the source time-domain indicator and the causal kernel.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Split actual lattice phases and eliminate dummy selected vertex clocks by Fubini. -/
theorem RootCoordinates.integral_selectedPhaseMixture {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (G : (Fin n → ((Fin d → ℤ) × (Fin d → ℤ))) → (Fin R.restCount → ℝ) → ℂ)
    (hF : Integrable (fun z : Fin n → LinkMixturePoint d =>
      (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ R.rootLinks)) (z i)) *
        G (fun i => (z i).1) (R.equiv (fun i => (z i).2)).2)
      (productLinkMixtureMeasure d n R.rootLinks)) :
    (∫ z : Fin n → LinkMixturePoint d,
      (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ R.rootLinks)) (z i)) *
        G (fun i => (z i).1) (R.equiv (fun i => (z i).2)).2
        ∂productLinkMixtureMeasure d n R.rootLinks) =
      ∫ p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)),
        (∫ u : Fin R.restCount → ℝ,
          (R.restBox Q).indicator (fun _ => R.remainingMixtureFactor L γ δ Q p u) u * G p u)
        ∂Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ R.rootLinks))) := by
  let F : (Fin n → LinkMixturePoint d) → ℂ := fun z =>
    (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ R.rootLinks)) (z i)) *
      G (fun i => (z i).1) (R.equiv (fun i => (z i).2)).2
  have hi : Integrable (fun z => F ((phaseTimeEquiv d n).symm z))
      ((Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ R.rootLinks)))).prod volume) :=
    (measurePreserving_phaseTimeEquiv d n R.rootLinks).symm.integrable_comp_of_integrable hF
  rw [integral_phaseTimeSplit_clocksFirst R.rootLinks _ hF]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with p hp
  exact R.integral_linkMixtureFactor_mul_remaining L γ δ Q p (G p) hp

end WaveTurbulence.Incoh
