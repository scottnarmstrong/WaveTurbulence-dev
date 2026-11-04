/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.GLeafToNode
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeIsDesc
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlower
public import WaveTurbulence.Frozen.Defs.LayeredGarden

/-!
# LayeredGarden.OnStem

Wave B tier B1 (WaveB1-Core.lean), source: T Def `defflower`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The **stem** of a flower tree: the ancestors of a flower (T Def `defflower`). -/
def OnStem (a : GNode LG.garden.tree) : Prop :=
  ∃ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ ∧ a.IsDesc ℓ.toNode

end LayeredGarden
end WaveTurbulence
