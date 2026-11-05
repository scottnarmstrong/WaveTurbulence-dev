/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SolutionTranslationMap
/-! Signed spatial phase covariance, for the exact momentum support of the cumulants. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set

/-- Signed coefficient arrays have precisely their integer gauge charges. -/
theorem signed_solution_joint_map_translation {d : ℕ} {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L γ δ T : ℝ} (hL : 0 < L)
    (φ : Mom d → ℝ) {g : (Fin d → ℤ) → Ω → ℂ} (hG : IsGaussianData μ g)
    (F : Set Ω) (hFm : MeasurableSet F) (hF : IsSymmetricEvent L φ g F)
    (a : Ω → ℝ → (Fin d → ℤ) → ℂ)
    (ha : ∀ ω ∈ F, IsASolution L γ δ T (initialCoeff L φ g ω) (a ω))
    (hrapid : ∀ ω ∈ F, IsRapidDecay (initialCoeff L φ g ω))
    (hmeas : ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω => a ω t n)
    (t : ι → Icc (0 : ℝ) T) (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ) (x : Mom d) :
    (μ.restrict F).map (fun ω j => zpowSign (ζ j) (a ω (t j) (n j))) =
      (μ.restrict F).map (fun ω j =>
        Complex.exp (((((ζ j : ℤ) : ℝ) * (-(2 * Real.pi * inner ℝ (latticePoint L (n j)) x)) : ℝ) : ℂ) * Complex.I) *
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
  have hp : Measurable (fun ω j => translationPhase L x (n j) * a ω (t j) (n j)) :=
    measurable_pi_iff.mpr fun j => (hmeas _ (t j).2 (n j)).const_mul _
  have h := congrArg (fun ν => ν.map S) (solution_joint_map_translation hL φ hG F hFm hF a ha hrapid t n x)
  rw [Measure.map_map hS hm, Measure.map_map hS hp] at h
  dsimp only [S, Function.comp_def, translationPhase] at h
  simpa only [zpowSign_gauge] using h


end WaveTurbulence.Induct
