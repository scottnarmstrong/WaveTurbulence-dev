/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SelectedMixtureIntegral

/-!
# Exact source integration in the selected vertex coordinates

The clock amplitude may contain the complete source ordering and literal
selected temporal phases. No rectangular-domain approximation is made.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Integrate the selected clocks of an actual phase-expanded source integrand. -/
theorem RootCoordinates.integral_selectedClockAmplitude {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)))
    (H : (Fin r → ℝ) × (Fin R.restCount → ℝ) → ℂ)
    (hF : Integrable (fun t : Fin n → Fin 2 → ℝ =>
      (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ R.rootLinks)) (p i, t i)) * H (R.equiv t))) :
    (∫ t : Fin n → Fin 2 → ℝ,
      (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ R.rootLinks)) (p i, t i)) * H (R.equiv t)) =
      ∫ u : Fin R.restCount → ℝ,
        (R.restBox Q).indicator (fun _ => R.remainingMixtureFactor L γ δ Q p u) u *
          ∫ v in R.rootBox Q, H (v, u) := by
  let F : (Fin n → Fin 2 → ℝ) → ℂ := fun t =>
    (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ R.rootLinks)) (p i, t i)) * H (R.equiv t)
  have hi : Integrable (fun z => F (R.equiv.symm z)) :=
    R.measurePreserving.symm.integrable_comp_of_integrable hF
  calc
    _ = ∫ z, F (R.equiv.symm z) := (R.measurePreserving.symm.integral_comp' F).symm
    _ = ∫ u : Fin R.restCount → ℝ, ∫ v : Fin r → ℝ, F (R.equiv.symm (v, u)) :=
      integral_prod_symm _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [F, MeasurableEquiv.apply_symm_apply]
      simp_rw [R.prod_linkMixtureFactor_eq_split]
      calc
        _ = ∫ v : Fin r → ℝ, (R.rootBox Q).indicator
            (fun v => (R.restBox Q).indicator (fun _ => R.remainingMixtureFactor L γ δ Q p u) u * H (v, u)) v := by
          apply integral_congr_ae
          filter_upwards [] with v
          by_cases hv : v ∈ R.rootBox Q <;> simp [hv]
        _ = _ := by
          rw [integral_indicator (show MeasurableSet (R.rootBox Q) from measurableSet_Icc), integral_const_mul]

end WaveTurbulence.Incoh
