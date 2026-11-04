/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.ZNorm

/-!
# ZSpace

Wave B tier B1 (WaveB1-System.lean), source: T L787; WAVE-B §2.5.3. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

/-- **The space `Z`** (T L787; WAVE-B §2.5.3 with Q16): arrays on `[p, p+1]`, continuous in time for
each `n`, with finite `Z^Λ` norm. -/
def ZSpace (L : ℝ) (Λ : ℝ) (p : ℕ) : Set (Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) :=
  {b | (∀ n, Continuous fun t => b t n) ∧ ZNorm L Λ b < ⊤}

end Norms
end WaveTurbulence
