/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# IsBalancedSig

Wave B tier B1 (WaveB1-Statements.lean), source: (file) WAVE-B v2 §4. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

/-- A balanced signature of width `2m`: exactly `m` plus signs. -/
def IsBalancedSig {w : ℕ} (ζ : Fin w → ℤˣ) : Prop := ∑ j, ((ζ j : ℤˣ) : ℤ) = 0

end WaveTurbulence
