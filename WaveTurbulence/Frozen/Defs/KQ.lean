/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.KQstar
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.Mom

/-!
# KQ

Wave B tier B1 (WaveB1-System.lean), source: T L678. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}
variable (L γ δ : ℝ) {d : ℕ}

/-- `K_𝒬(t, k) := K*_𝒬(t, t, k)` (T L678). -/
noncomputable def KQ (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (t : ℝ) (k : Mom d) : ℂ :=
  KQstar L γ δ F LG t t k

end Kernels
end WaveTurbulence
