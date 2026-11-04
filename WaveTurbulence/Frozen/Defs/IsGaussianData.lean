/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.StdComplexGaussian

/-!
# IsGaussianData

Wave B tier B1 (WaveB1-Statements.lean), source: (file) WAVE-B v2 §4. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence

/-- The probability data of Wave A (`main`): `g_n` measurable, independent, each of law
`stdComplexGaussian`. -/
def IsGaussianData {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : (Fin d → ℤ) → Ω → ℂ) : Prop :=
  (∀ n, Measurable (g n)) ∧ iIndepFun g μ ∧ ∀ n, μ.map (g n) = stdComplexGaussian

end WaveTurbulence
