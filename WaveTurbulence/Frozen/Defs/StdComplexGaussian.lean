/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# StdComplexGaussian

Deng–Hani, L292-L294; DH21 L297; DH19 L140. Frozen by ruling D6 (`docs/DECISIONS.md#D6`); do not edit.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped InnerProductSpace SchwartzMap ENNReal

namespace WaveTurbulence

/-- The law of a centered normalized complex Gaussian `g` (`𝔼 g = 0`, `𝔼|g|² = 1`, circularly
symmetric): real and imaginary parts independent `N(0, 1/2)`. -/
def stdComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))).map Complex.equivRealProd.symm

end WaveTurbulence
