/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# resFactor

Wave B tier B1 (WaveB1-Core.lean), source: T (res). Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Decorations

variable {w : ℕ} (G : Garden w)

/-- The resonance factor `Ω(k₁,k₂,k₃,k) = |k₁|² - |k₂|² + |k₃|² - |k|²` (T (res)). -/
noncomputable def resFactor {d : ℕ} (k₁ k₂ k₃ k : Mom d) : ℝ :=
  ‖k₁‖ ^ 2 - ‖k₂‖ ^ 2 + ‖k₃‖ ^ 2 - ‖k‖ ^ 2

end Decorations
end WaveTurbulence
