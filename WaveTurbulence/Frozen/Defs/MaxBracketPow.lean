/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# maxBracketPow

Wave B tier B1 (WaveB1-System.lean), source: T (normX). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

/-- `(max_i ⟨λ_i⟩)^θ` (T (normX)); `1` for `r = 0`. Correct for every `θ ∈ ℝ`: `max_i (⟨λ_i⟩^θ)`
would take the minimum bracket when `θ < 0` (stage-2 audit R3). Since `⟨λ⟩ ≥ 1`, the `⊔ 1` changes
nothing for `r ≥ 1`. -/
noncomputable def maxBracketPow {r : ℕ} (θ : ℝ) (lam : Fin r → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((⨆ i, Real.sqrt (1 + lam i ^ 2)) ⊔ 1) ^ θ)

end Norms
end WaveTurbulence
