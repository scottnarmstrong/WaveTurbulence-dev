/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.Measurability
public import WaveTurbulence.Foundations.MainGlue.SmoothData

/-!
# Measurable arbitrary coefficient data in the NLS bridge

TARGET L817–L819, FINDINGS F8: the existence event and truncated observable
are measurable for any measurable coefficient map, independent of a choice
of envelope for the initial data.
-/

public section

noncomputable section

open MeasureTheory Set

namespace WaveTurbulence.NLS

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The source existence event is measurable for an arbitrary measurable initial-data map. -/
theorem bridge_measurableSet_solvable {L α γ T : ℝ} (hL : 0 < L) (hT : 0 < T)
    (hα : α = L ^ (-γ)) {c : Ω → (Fin d → ℤ) → ℂ} (hc : Measurable c) :
    MeasurableSet {ω | ∃ v, IsSmoothNLSSolution L α T (c ω) v} :=
  (MainGlue.measurableSet_smoothDataSet hL hT hα).preimage hc

/-- The source energy observable is measurable for every admissible selection of solutions. -/
theorem bridge_measurable_indicator_energy {L α γ T : ℝ} (hL : 0 < L) (hT : 0 < T)
    (hα : α = L ^ (-γ)) {c : Ω → (Fin d → ℤ) → ℂ} (hc : Measurable c)
    (U : Ω → ℝ → (Fin d → ℝ) → ℂ)
    (hU : ∀ ω, (∃ v, IsSmoothNLSSolution L α T (c ω) v) → IsSmoothNLSSolution L α T (c ω) (U ω))
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : Fin d → ℤ) :
    Measurable ({ω | ∃ v, IsSmoothNLSSolution L α T (c ω) v}.indicator
      (fun ω => ‖torusFourierCoeff L (U ω t) n‖ ^ 2)) := by
  have hi (ω : Ω) : initialCoeff L (fun _ : Mom d => 1) (fun n ω => c ω n) ω = c ω := by
    ext m
    simp only [initialCoeff, Real.sqrt_one, Complex.ofReal_one, one_mul]
  have he : solvableEvent L α T (fun _ : Mom d => 1) (fun n ω => c ω n) =
      {ω | ∃ v, IsSmoothNLSSolution L α T (c ω) v} := by
    ext ω
    simp only [solvableEvent, hi, mem_ofPred_eq]
  have hU' : ∀ ω ∈ solvableEvent L α T (fun _ : Mom d => 1) (fun n ω => c ω n),
      IsSmoothNLSSolution L α T (initialCoeff L (fun _ : Mom d => 1) (fun n ω => c ω n) ω) (U ω) := by
    intro ω hω
    rw [hi]
    exact hU ω (by rwa [he] at hω)
  have H := measurable_indicator_norm_torusFourierCoeff_sq hL hT hα (fun _ : Mom d => 1)
    (fun n => (measurable_pi_apply n).comp hc) U hU' ht n
  simpa only [Function.comp_def, he] using H

end WaveTurbulence.NLS
