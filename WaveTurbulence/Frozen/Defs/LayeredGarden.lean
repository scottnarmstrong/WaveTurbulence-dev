/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.IsLayering

/-!
# LayeredGarden

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `deflayer`, L649–L656. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- A **layered garden** of width `w`. -/
structure LayeredGarden (w : ℕ) where
  /-- the garden -/
  garden : Garden w
  /-- the layers `𝔏_𝔫` -/
  layer : GNode garden.tree → ℕ
  isLayering : IsLayering garden layer

end WaveTurbulence
