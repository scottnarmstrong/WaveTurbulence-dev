/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.SNorm

/-!
# SNormR

Wave B tier B1 (WaveB1-System.lean), source: T (normX2), L585. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Norms

variable {d : ℕ}

/-- **`‖F‖_{𝔖^{Λ₁,Λ₂}}`** of a real function on `ℝ^d` (T (normX2), L585). -/
noncomputable def SNormR (Λ₁ Λ₂ : ℕ) (F : Mom d → ℝ) : ℝ≥0∞ :=
  SNorm Λ₁ Λ₂ (fun k => (F k : ℂ))

end Norms
end WaveTurbulence
