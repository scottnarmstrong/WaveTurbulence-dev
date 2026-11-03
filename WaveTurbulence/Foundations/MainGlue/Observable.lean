/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.MainGlue.SmoothData

/-!
# G2: a measurable Fourier-energy observable on the coefficient space

SEAL-PLAN §B.4 G2. Choose a smooth solution on the smooth-data set and
extend its energy observable by zero off that set. The landed truncated-flow
measurability theorem proves this extension measurable. Uniqueness makes
its value independent of the chosen smooth solution.
-/

public section

namespace WaveTurbulence.MainGlue
open MeasureTheory Set
open scoped Classical

/-- A choice of actual smooth solution on its existence set, extended by zero elsewhere. -/
@[expose] noncomputable def chosenSmoothSolution {d : ℕ} (L α T : ℝ)
    (c : (Fin d → ℤ) → ℂ) : ℝ → (Fin d → ℝ) → ℂ :=
  if h : c ∈ NLS.smoothDataSet L α T then Classical.choose h else fun _ _ => 0

theorem chosenSmoothSolution_spec {d : ℕ} {L α T : ℝ} {c : (Fin d → ℤ) → ℂ}
    (hc : c ∈ NLS.smoothDataSet L α T) :
    IsSmoothNLSSolution L α T c (chosenSmoothSolution L α T c) := by
  rw [chosenSmoothSolution, dite_eq_left hc]
  exact Classical.choose_spec hc

/-- The energy observable is zero outside the smooth-data set. -/
@[expose] noncomputable def fourierEnergyObservable {d : ℕ} (L α T t : ℝ) (n : Fin d → ℤ) :
    ((Fin d → ℤ) → ℂ) → ℝ :=
  (NLS.smoothDataSet L α T).indicator
    (fun c => ‖torusFourierCoeff L (chosenSmoothSolution L α T c t) n‖ ^ 2)

private theorem initialCoeff_coordinate_identity {d : ℕ} (L : ℝ) (c : (Fin d → ℤ) → ℂ) :
    initialCoeff L (fun _ : Mom d => 1) (fun n (c : (Fin d → ℤ) → ℂ) => c n) c = c := by
  ext n
  simp [initialCoeff]

/-- The unit envelope and coordinate random variables realize the identity data map. -/
theorem solvableEvent_coordinate_identity {d : ℕ} (L α T : ℝ) :
    solvableEvent L α T (fun _ : Mom d => 1) (fun n (c : (Fin d → ℤ) → ℂ) => c n) =
      NLS.smoothDataSet L α T := by
  rw [NLS.solvableEvent_eq_preimage]
  simp only [initialCoeff_coordinate_identity]
  rfl

/-- G2: the zero extension of the solution's Fourier energy is measurable. -/
theorem measurable_fourierEnergyObservable {d : ℕ} {L α γ T t : ℝ} (hL : 0 < L)
    (hT : 0 < T) (hα : α = L ^ (-γ)) (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    Measurable (fourierEnergyObservable L α T t n) := by
  have hU : ∀ c ∈ solvableEvent L α T (fun _ : Mom d => 1)
      (fun n (c : (Fin d → ℤ) → ℂ) => c n),
      IsSmoothNLSSolution L α T
        (initialCoeff L (fun _ : Mom d => 1) (fun n (c : (Fin d → ℤ) → ℂ) => c n) c)
        (chosenSmoothSolution L α T c) := by
    intro c hc
    rw [initialCoeff_coordinate_identity]
    exact chosenSmoothSolution_spec (by rwa [solvableEvent_coordinate_identity] at hc)
  have h := NLS.measurable_indicator_norm_torusFourierCoeff_sq hL hT hα
    (fun _ : Mom d => 1) (fun n => measurable_pi_apply n) (chosenSmoothSolution L α T) hU ht n
  simpa only [solvableEvent_coordinate_identity, fourierEnergyObservable] using h

/-- The observable agrees with every smooth solution having these coefficients. -/
theorem fourierEnergyObservable_eq {d : ℕ} {L α T t : ℝ} (hL : 0 < L)
    {c : (Fin d → ℤ) → ℂ} (hc : c ∈ NLS.smoothDataSet L α T)
    {u : ℝ → (Fin d → ℝ) → ℂ} (hu : IsSmoothNLSSolution L α T c u)
    (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    ‖torusFourierCoeff L (u t) n‖ ^ 2 = fourierEnergyObservable L α T t n c := by
  rw [fourierEnergyObservable, Set.indicator_of_mem hc]
  rw [hu.eq_of_eq hL (chosenSmoothSolution_spec hc) ht]

/-- G2 in the existential form proposed by SEAL-PLAN §B.4. -/
theorem exists_measurable_fourier_energy {d : ℕ} {L α γ T : ℝ} (hL : 0 < L)
    (hT : 0 < T) (hα : α = L ^ (-γ)) {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    ∃ Φ : ((Fin d → ℤ) → ℂ) → ℝ, Measurable Φ ∧
      ∀ c ∈ NLS.smoothDataSet L α T, ∀ u, IsSmoothNLSSolution L α T c u →
        ‖torusFourierCoeff L (u t) n‖ ^ 2 = Φ c :=
  ⟨fourierEnergyObservable L α T t n, measurable_fourierEnergyObservable hL hT hα ht n,
    fun _ hc _ hu => fourierEnergyObservable_eq hL hc hu ht n⟩

end WaveTurbulence.MainGlue
