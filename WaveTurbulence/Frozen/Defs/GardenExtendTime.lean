/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenFreeBranch
public import WaveTurbulence.Frozen.Defs.GardenIsFlowerParent
public import WaveTurbulence.Frozen.Defs.InstDecidableIsFlowerParent

/-!
# Garden.extendTime

Wave B tier B1 (WaveB1-System.lean), source: (file) WAVE-B §2.3; T L545–L564; T Def `defcm`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

section Kernels

variable {w : ℕ}

/-- Times of all branching nodes from the free times, the flower parents getting the time `s`. -/
def Garden.extendTime (G : Garden w) (s : ℝ) (τ : G.FreeBranch → ℝ) : GBranch G.tree → ℝ :=
  fun b => if h : G.IsFlowerParent b then s else τ ⟨b, h⟩

end Kernels
end WaveTurbulence
