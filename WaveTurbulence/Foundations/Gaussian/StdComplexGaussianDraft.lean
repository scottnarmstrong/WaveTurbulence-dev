/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The normalized complex Gaussian law (DRAFT copy)

Verbatim copy of the orchestrator's DRAFT definition `stdComplexGaussian` (packet GAUSS-HC brief),
placed here because packet CUMUL has not yet landed `ComplexGaussian.lean`. The orchestrator will
reconcile the two copies at landing.
-/

public section

open MeasureTheory ProbabilityTheory

namespace WaveTurbulence

/-- The law of a centered normalized complex Gaussian `g` (`𝔼 g = 0`, `𝔼|g|² = 1`, circularly
symmetric): real and imaginary parts independent `N(0, 1/2)`. -/
@[expose] noncomputable def stdComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))).map Complex.equivRealProd.symm

instance : IsProbabilityMeasure stdComplexGaussian := by
  unfold stdComplexGaussian
  infer_instance

end WaveTurbulence
