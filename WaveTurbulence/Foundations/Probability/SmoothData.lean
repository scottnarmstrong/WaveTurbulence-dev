/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Probability.RandomRapidDecay
public import WaveTurbulence.Foundations.Probability.WeightedLatticeSummability

/-!
# Smooth Gaussian initial data with Schwartz envelope

TARGET (DAT), L290–L293. On one full-measure event, the frozen initial
coefficients have finite absolute sums against every real Japanese-bracket
weight and their torus Fourier series is smooth. The bracket convention is
`⟨k⟩^s = (1+‖k‖²)^(s/2)`, as in the campaign's frozen weighted norm.
-/

public section

namespace WaveTurbulence.Probability
open MeasureTheory ProbabilityTheory
open scoped ContDiff SchwartzMap

/-- TARGET's weighted summability and smooth initial-data assertion, on one
full-measure event valid simultaneously for every real weight exponent. -/
theorem ae_summable_all_real_weights_and_smooth {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {L : ℝ} (hL : 0 < L)
    (φ : 𝓢(Mom d, ℝ)) (g : (Fin d → ℤ) → Ω → ℂ)
    (hg : ∀ n, HasLaw (g n) stdComplexGaussian P) :
    ∀ᵐ ξ ∂P,
      (∀ s : ℝ, Summable (fun n => (1 + ‖latticePoint L n‖ ^ 2) ^ (s / 2) *
        Real.sqrt (φ (latticePoint L n)) * ‖g n ξ‖)) ∧
      ContDiff ℝ ∞ (torusSeries L (initialCoeff L φ g ξ)) := by
  filter_upwards [ae_initialCoeff_isRapidDecay hL φ g hg] with ξ hξ
  refine ⟨?_, contDiff_torusSeries hL hξ⟩
  intro s
  have h := summable_real_weight_of_isRapidDecay hL hξ s
  simpa only [initialCoeff, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), ← mul_assoc] using h

end WaveTurbulence.Probability
