/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsLone
public import WaveTurbulence.Frozen.Defs.InstFintypeGLeaf
public import WaveTurbulence.Frozen.Defs.MarkTag

/-!
# IsPairedTree

Wave B tier B1 (WaveB1-Core.lean), source: T L637. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- A **paired tree** (T L637): one tree whose leaves are paired except one, the lone leaf (marked
`lower`). -/
def IsPairedTree (G : Garden 1) : Prop :=
  (Finset.univ.filter fun ℓ : GLeaf G.tree => G.mark ℓ ≠ none).card = 1 ∧
    ∀ ℓ, G.mark ℓ ≠ none → G.IsLone ℓ

end WaveTurbulence
