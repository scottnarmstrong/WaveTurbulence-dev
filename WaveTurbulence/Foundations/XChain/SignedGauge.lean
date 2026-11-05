/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SolutionGaugeMap
public import WaveTurbulence.Foundations.Cumulant.Symmetry
/-! The signed gauge charge and unbalanced cumulant support in TARGET S2. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set

theorem zpowSign_gauge (ζ : ℤˣ) (θ : ℝ) (z : ℂ) :
    zpowSign ζ (Complex.exp ((θ : ℂ) * Complex.I) * z) =
      Complex.exp (((((ζ : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) * zpowSign ζ z := by
  rcases Int.units_eq_one_or ζ with rfl | rfl
  · simp [zpowSign]
  · simp [zpowSign, map_mul, ← Complex.exp_conj]

/-- Signed coefficient arrays have precisely their integer gauge charges. -/
theorem signed_solution_joint_map_gauge {d : ℕ} {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L γ δ T : ℝ} (hL : 0 < L)
    (φ : Mom d → ℝ) {g : (Fin d → ℤ) → Ω → ℂ} (hG : IsGaussianData μ g)
    (F : Set Ω) (hFm : MeasurableSet F) (hF : IsSymmetricEvent L φ g F)
    (a : Ω → ℝ → (Fin d → ℤ) → ℂ)
    (ha : ∀ ω ∈ F, IsASolution L γ δ T (initialCoeff L φ g ω) (a ω))
    (hrapid : ∀ ω ∈ F, IsRapidDecay (initialCoeff L φ g ω))
    (hmeas : ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω => a ω t n)
    (t : ι → Icc (0 : ℝ) T) (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) (θ : ℝ) :
    (μ.restrict F).map (fun ω j => zpowSign (ζ j) (a ω (t j) (n j))) =
      (μ.restrict F).map (fun ω j =>
        Complex.exp (((((ζ j : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) *
          zpowSign (ζ j) (a ω (t j) (n j))) := by
  let S := fun (x : ι → ℂ) j => zpowSign (ζ j) (x j)
  have hS : Measurable S := by
    apply measurable_pi_iff.mpr
    intro j
    dsimp only [S]
    unfold zpowSign
    split_ifs
    · exact measurable_pi_apply j
    · exact Complex.continuous_conj.measurable.comp (measurable_pi_apply j)
  have hm : Measurable (fun ω j => a ω (t j) (n j)) :=
    measurable_pi_iff.mpr fun j => hmeas _ (t j).2 (n j)
  have hp : Measurable (fun ω j => Complex.exp ((θ : ℂ) * Complex.I) * a ω (t j) (n j)) :=
    measurable_pi_iff.mpr fun j => (hmeas _ (t j).2 (n j)).const_mul _
  have h := congrArg (fun ν => ν.map S) (solution_joint_map_gauge hL φ hG F hFm hF a ha hrapid t n θ)
  rw [Measure.map_map hS hm, Measure.map_map hS hp] at h
  dsimp only [S, Function.comp_def] at h
  simpa only [zpowSign_gauge] using h

/-- Gauge symmetry kills every cumulant of nonzero total signed charge. -/
theorem cumulant_signed_solution_eq_zero_of_unbalanced {d : ℕ} {Ω ι : Type*}
    [MeasurableSpace Ω] [DecidableEq ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {L γ δ T : ℝ} (hL : 0 < L) (φ : Mom d → ℝ)
    {g : (Fin d → ℤ) → Ω → ℂ} (hG : IsGaussianData μ g)
    (F : Set Ω) (hFm : MeasurableSet F) (hF : IsSymmetricEvent L φ g F)
    (a : Ω → ℝ → (Fin d → ℤ) → ℂ)
    (ha : ∀ ω ∈ F, IsASolution L γ δ T (initialCoeff L φ g ω) (a ω))
    (hrapid : ∀ ω ∈ F, IsRapidDecay (initialCoeff L φ g ω))
    (hmeas : ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω => a ω t n)
    (t : ι → Icc (0 : ℝ) T) (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) (s : Finset ι)
    (hq : (∑ j ∈ s, (ζ j : ℤ)) ≠ 0) :
    cumulant (μ.restrict F) (fun j ω => zpowSign (ζ j) (a ω (t j) (n j))) s = 0 := by
  apply cumulant_eq_zero_of_gauge_invariant (q := fun j => ((ζ j : ℤ) : ℝ))
  · intro j
    have hj := hmeas _ (t j).2 (n j)
    unfold zpowSign
    split_ifs
    · exact hj
    · exact Complex.continuous_conj.measurable.comp hj
  · exact fun θ => signed_solution_joint_map_gauge hL φ hG F hFm hF a ha hrapid hmeas t n ζ θ
  · exact_mod_cast hq

end WaveTurbulence.Induct
