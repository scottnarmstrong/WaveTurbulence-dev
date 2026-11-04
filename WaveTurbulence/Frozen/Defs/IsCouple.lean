/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsPlain

/-!
# IsCouple

Wave B tier B1 (WaveB1-Core.lean), source: T L634–L635. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- A **couple** (T L634–L635): a plain garden of width `2` with signature `(+,-)`; its trees are
`𝒯⁺ = tree 0` and `𝒯⁻ = tree 1`. -/
def IsCouple (G : Garden 2) : Prop := G.IsPlain ∧ G.sig = ![1, -1]

end WaveTurbulence
