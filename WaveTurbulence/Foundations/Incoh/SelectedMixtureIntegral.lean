/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SelectedMixtureFactorization

/-!
# Exact integration of the dummy selected clocks

Finite coordinate measure preservation and Fubini reduce the literal
mixture to the remaining clocks. This is an integral identity, not an estimate.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Eliminate the selected dummy clocks while retaining arbitrary remaining-clock dependence. -/
theorem RootCoordinates.integral_linkMixtureFactor_mul_remaining {d n r : ℕ}
    (R : RootCoordinates n r) (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ))) (G : (Fin R.restCount → ℝ) → ℂ)
    (hF : Integrable (fun t : Fin n → Fin 2 → ℝ =>
      (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ R.rootLinks)) (p i, t i)) *
        G (R.equiv t).2)) :
    (∫ t : Fin n → Fin 2 → ℝ,
      (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ R.rootLinks)) (p i, t i)) *
        G (R.equiv t).2) =
      ∫ u : Fin R.restCount → ℝ,
        (R.restBox Q).indicator (fun _ => R.remainingMixtureFactor L γ δ Q p u) u * G u := by
  let F : (Fin n → Fin 2 → ℝ) → ℂ := fun t =>
    (∏ i, linkMixtureFactor L γ δ (Q i) (decide (i ∈ R.rootLinks)) (p i, t i)) * G (R.equiv t).2
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
      rw [integral_mul_const, R.integral_dummyMixtureFactor]

end WaveTurbulence.Incoh
