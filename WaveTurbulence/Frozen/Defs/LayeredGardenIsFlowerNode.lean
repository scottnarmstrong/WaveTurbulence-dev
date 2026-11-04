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
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.GardenIsFlower
public import WaveTurbulence.Frozen.Defs.LayeredGarden

/-!
# LayeredGarden.IsFlowerNode

Wave B tier B1 (WaveB1-Flower.lean), source: (file) T L2327; T L2283–L2285; T L2331. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- `ℓ`'s node is a flower. -/
def IsFlowerNode (a : GNode LG.garden.tree) : Prop :=
  ∃ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ ∧ ℓ.toNode = a

end LayeredGarden
end WaveTurbulence
