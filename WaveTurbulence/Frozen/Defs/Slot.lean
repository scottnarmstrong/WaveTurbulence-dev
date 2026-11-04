/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# Slot

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Duhamel

variable (L γ δ : ℝ) {d : ℕ}

/-- An input slot of the trilinear form: `none` is the unknown `b`, `some N` is `𝒥_N`. -/
abbrev Slot (Ntr : ℕ) := Option (Fin (Ntr + 1))

end Duhamel
end WaveTurbulence
