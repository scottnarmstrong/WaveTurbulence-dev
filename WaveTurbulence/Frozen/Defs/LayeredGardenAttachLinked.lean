/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeLeavesBelow
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.LayeredGarden

/-!
# LayeredGarden.AttachLinked

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `defgtr`, L731–L732. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- Two nodes are linked if some leaf below the first is paired with a leaf below the second. -/
def AttachLinked (u u' : GNode LG.garden.tree) : Prop :=
  ∃ ℓ ∈ u.leavesBelow, LG.garden.pair ℓ ∈ u'.leavesBelow

end LayeredGarden
end WaveTurbulence
