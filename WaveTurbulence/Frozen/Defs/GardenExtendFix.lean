/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.Garden

/-!
# Garden.extendFix

Wave B tier B1 (WaveB1-Flower.lean), source: (file) T L2327; T L2283–L2285; T L2331. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section General

variable {w : ℕ}

/-- Branch times from the free times: a designated node `b` (`fix b = some v`) gets the time `v`. -/
def Garden.extendFix (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) : GBranch G.tree → ℝ :=
  fun b => match h : fix b with
    | some v => v
    | none => τ ⟨b, h⟩

end General
end WaveTurbulence
