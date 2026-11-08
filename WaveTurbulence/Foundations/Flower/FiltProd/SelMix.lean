/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltProd.Mix
public import WaveTurbulence.Foundations.Incoh.SelectedClockIntegral
public import WaveTurbulence.Foundations.Incoh.SelectedPhaseMixture
public import WaveTurbulence.Foundations.Incoh.PhaseCoordinateIntegral

/-! # D5b-2 FILT-PROD: selected clocks and phase mixtures (twins of `SelectedMixtureFactorization`, `SelectedMixtureIntegral`, `SelectedPhaseMixture`, `SelectedClockIntegral`) -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltProd
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc


/-- Literal selected coefficients and untouched link factors at the remaining clocks. -/
def RootCoordinates.remainingMixtureFactorFilt {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ))) (u : Fin R.restCount → ℝ) : ℂ :=
  ∏ i, if i ∈ R.rootLinks then filtLinkPhaseCoefficient L (Q i) (φ i) (p i)
    else filtLinkTimeFactor L γ δ (Q i) (φ i) (R.equiv.symm (0, u) i)

/-- Every clock cutoff remains present after factoring the selected coefficients. -/
theorem RootCoordinates.prod_linkMixtureFactor_eq_indicatorFilt {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)))
    (v : Fin r → ℝ) (u : Fin R.restCount → ℝ) :
    (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ R.rootLinks))
      (p i, R.equiv.symm (v, u) i)) =
      (univ.pi (fun i => linkBox (Q i))).indicator
        (fun _ => RootCoordinates.remainingMixtureFactorFilt R L γ δ Q φ p u) (R.equiv.symm (v, u)) := by
  classical
  by_cases hbox : R.equiv.symm (v, u) ∈ univ.pi (fun i => linkBox (Q i))
  · rw [indicator_of_mem hbox]
    unfold RootCoordinates.remainingMixtureFactorFilt
    apply Finset.prod_congr rfl
    intro i _
    rw [linkMixtureFactorFilt, indicator_of_mem (hbox i (mem_univ i))]
    by_cases hi : i ∈ R.rootLinks
    · simp only [hi, decide_true, ite_true]
    · simp only [hi, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [R.equiv_symm_eq_of_notMem_rootLinks v 0 u i hi]
  · rw [indicator_of_notMem hbox]
    have hi : ∃ i, R.equiv.symm (v, u) i ∉ linkBox (Q i) := by
      simpa only [mem_pi, mem_univ, forall_const, not_forall] using hbox
    obtain ⟨i, hi⟩ := hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact indicator_of_notMem hi _

/-- The selected dummy clocks contribute precisely their unit layer-box indicator. -/
theorem RootCoordinates.prod_linkMixtureFactor_eq_splitFilt {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)))
    (v : Fin r → ℝ) (u : Fin R.restCount → ℝ) :
    (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ R.rootLinks))
      (p i, R.equiv.symm (v, u) i)) =
      (R.rootBox Q).indicator (fun _ =>
        (R.restBox Q).indicator (fun _ => RootCoordinates.remainingMixtureFactorFilt R L γ δ Q φ p u) u) v := by
  rw [RootCoordinates.prod_linkMixtureFactor_eq_indicatorFilt R]
  by_cases hv : v ∈ R.rootBox Q <;> by_cases hu : u ∈ R.restBox Q <;>
    simp [R.equiv_symm_mem_linkBoxes, hv, hu]

/-- Integrating the dummy selected clocks costs exactly their unit box volume. -/
theorem RootCoordinates.integral_dummyMixtureFactorFilt {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ))) (u : Fin R.restCount → ℝ) :
    (∫ v : Fin r → ℝ, ∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ R.rootLinks))
      (p i, R.equiv.symm (v, u) i)) =
      (R.restBox Q).indicator (fun _ => RootCoordinates.remainingMixtureFactorFilt R L γ δ Q φ p u) u := by
  simp_rw [RootCoordinates.prod_linkMixtureFactor_eq_splitFilt R L γ δ Q φ p]
  rw [integral_indicator (show MeasurableSet (R.rootBox Q) from measurableSet_Icc), setIntegral_const, measureReal_def,
    R.volume_rootBox Q, ENNReal.toReal_one, one_smul]



/-- Eliminate the selected dummy clocks while retaining arbitrary remaining-clock dependence. -/
theorem RootCoordinates.integral_linkMixtureFactor_mul_remainingFilt {d n r : ℕ}
    (R : RootCoordinates n r) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ))) (G : (Fin R.restCount → ℝ) → ℂ)
    (hF : Integrable (fun t : Fin n → Fin 2 → ℝ =>
      (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ R.rootLinks)) (p i, t i)) *
        G (R.equiv t).2)) :
    (∫ t : Fin n → Fin 2 → ℝ,
      (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ R.rootLinks)) (p i, t i)) *
        G (R.equiv t).2) =
      ∫ u : Fin R.restCount → ℝ,
        (R.restBox Q).indicator (fun _ => RootCoordinates.remainingMixtureFactorFilt R L γ δ Q φ p u) u * G u := by
  let F : (Fin n → Fin 2 → ℝ) → ℂ := fun t =>
    (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ R.rootLinks)) (p i, t i)) * G (R.equiv t).2
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
      rw [integral_mul_const, RootCoordinates.integral_dummyMixtureFactorFilt R]



/-- Split actual lattice phases and eliminate dummy selected vertex clocks by Fubini. -/
theorem RootCoordinates.integral_selectedPhaseMixtureFilt {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (G : (Fin n → ((Fin d → ℤ) × (Fin d → ℤ))) → (Fin R.restCount → ℝ) → ℂ)
    (hF : Integrable (fun z : Fin n → LinkMixturePoint d =>
      (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ R.rootLinks)) (z i)) *
        G (fun i => (z i).1) (R.equiv (fun i => (z i).2)).2)
      (productLinkMixtureMeasure d n R.rootLinks)) :
    (∫ z : Fin n → LinkMixturePoint d,
      (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ R.rootLinks)) (z i)) *
        G (fun i => (z i).1) (R.equiv (fun i => (z i).2)).2
        ∂productLinkMixtureMeasure d n R.rootLinks) =
      ∫ p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)),
        (∫ u : Fin R.restCount → ℝ,
          (R.restBox Q).indicator (fun _ => RootCoordinates.remainingMixtureFactorFilt R L γ δ Q φ p u) u * G p u)
        ∂Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ R.rootLinks))) := by
  let F : (Fin n → LinkMixturePoint d) → ℂ := fun z =>
    (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ R.rootLinks)) (z i)) *
      G (fun i => (z i).1) (R.equiv (fun i => (z i).2)).2
  have hi : Integrable (fun z => F ((phaseTimeEquiv d n).symm z))
      ((Measure.pi (fun i => phaseCoordinateMeasure d (decide (i ∈ R.rootLinks)))).prod volume) :=
    (measurePreserving_phaseTimeEquiv d n R.rootLinks).symm.integrable_comp_of_integrable hF
  rw [integral_phaseTimeSplit_clocksFirst R.rootLinks _ hF]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with p hp
  exact RootCoordinates.integral_linkMixtureFactor_mul_remainingFilt R L γ δ Q φ p (G p) hp



/-- Integrate the selected clocks of an actual phase-expanded source integrand. -/
theorem RootCoordinates.integral_selectedClockAmplitudeFilt {d n r : ℕ} (R : RootCoordinates n r)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (φ : Fin n → ℝ → ℂ)
    (p : Fin n → ((Fin d → ℤ) × (Fin d → ℤ)))
    (H : (Fin r → ℝ) × (Fin R.restCount → ℝ) → ℂ)
    (hF : Integrable (fun t : Fin n → Fin 2 → ℝ =>
      (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ R.rootLinks)) (p i, t i)) * H (R.equiv t))) :
    (∫ t : Fin n → Fin 2 → ℝ,
      (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ R.rootLinks)) (p i, t i)) * H (R.equiv t)) =
      ∫ u : Fin R.restCount → ℝ,
        (R.restBox Q).indicator (fun _ => RootCoordinates.remainingMixtureFactorFilt R L γ δ Q φ p u) u *
          ∫ v in R.rootBox Q, H (v, u) := by
  let F : (Fin n → Fin 2 → ℝ) → ℂ := fun t =>
    (∏ i, linkMixtureFactorFilt L γ δ (Q i) (φ i) (decide (i ∈ R.rootLinks)) (p i, t i)) * H (R.equiv t)
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
      simp_rw [RootCoordinates.prod_linkMixtureFactor_eq_splitFilt R]
      calc
        _ = ∫ v : Fin r → ℝ, (R.rootBox Q).indicator
            (fun v => (R.restBox Q).indicator (fun _ => RootCoordinates.remainingMixtureFactorFilt R L γ δ Q φ p u) u * H (v, u)) v := by
          apply integral_congr_ae
          filter_upwards [] with v
          by_cases hv : v ∈ R.rootBox Q <;> simp [hv]
        _ = _ := by
          rw [integral_indicator (show MeasurableSet (R.rootBox Q) from measurableSet_Icc), integral_const_mul]


end WaveTurbulence.Flower.FiltProd
