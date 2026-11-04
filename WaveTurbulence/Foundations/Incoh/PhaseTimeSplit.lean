/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.PhaseCoordinateIntegral
public import WaveTurbulence.Foundations.Incoh.ProductLinkMixture
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Separating lattice phases from vertex clocks

The literal product mixture measure splits into its phase and time
coordinates by a measure-preserving finite product equivalence.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- Split the phase and time arrays without changing their coordinates. -/
@[expose] def phaseTimeEquiv (d n : ℕ) :
    (Fin n → LinkMixturePoint d) ≃ᵐ
      ((Fin n → ((Fin d → ℤ) × (Fin d → ℤ))) × (Fin n → Fin 2 → ℝ)) :=
  MeasurableEquiv.arrowProdEquivProdArrow _ _ _

/-- The literal mixture measure is the product of its phase and time measures. -/
theorem measurePreserving_phaseTimeEquiv (d n : ℕ) (J : Finset (Fin n)) :
    MeasurePreserving (phaseTimeEquiv d n) (productLinkMixtureMeasure d n J)
      ((Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ J)))).prod volume) := by
  exact measurePreserving_arrowProdEquivProdArrow _ _ _
    (fun i => phaseCoordinateMeasure d (decide (i ∈ J))) (fun _ => volume)

/-- Fubini for the literal mixture, with all lattice phases integrated first. -/
theorem integral_phaseTimeSplit {d n : ℕ} (J : Finset (Fin n))
    (F : (Fin n → LinkMixturePoint d) → ℂ)
    (hF : Integrable F (productLinkMixtureMeasure d n J)) :
    (∫ z, F z ∂productLinkMixtureMeasure d n J) =
      ∫ t : Fin n → Fin 2 → ℝ,
        ∫ p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)),
          F (fun i => (p i, t i))
          ∂Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ J))) := by
  let e := phaseTimeEquiv d n
  have hp := measurePreserving_phaseTimeEquiv d n J
  have hi : Integrable (fun z => F (e.symm z))
      ((Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ J)))).prod volume) :=
    (hp.symm e).integrable_comp_of_integrable hF
  calc
    _ = ∫ z, F (e.symm z)
        ∂((Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ J)))).prod volume) :=
      ((hp.symm e).integral_comp' F).symm
    _ = _ := integral_prod_symm _ hi

end WaveTurbulence.Incoh
