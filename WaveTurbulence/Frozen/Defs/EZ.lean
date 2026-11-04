/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# eZ

Wave B tier B1 (WaveB1-Statements.lean), source: (file) WAVE-B v2 §4. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

/-- `e(z) = e^{2πiz}`. -/
noncomputable def eZ (z : ℝ) : ℂ := Complex.exp ((2 * Real.pi * z : ℝ) * Complex.I)

end WaveTurbulence
