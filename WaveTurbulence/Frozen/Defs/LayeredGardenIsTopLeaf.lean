/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenParentLayer
public import WaveTurbulence.Frozen.Defs.TTreeLeaves
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# LayeredGarden.IsTopLeaf

Wave B tier B1 (WaveB1-Flower.lean), source: T L2283. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The **leaves of the initial flower trees** (T L2283, L2294). These are the non-root nodes with a
layer-`p` parent that are leaves or lie in a lower layer: the paired layer-`p` leaves, the flower, and the
roots of the attached gardens. -/
def IsTopLeaf (p : ℕ) (a : GNode LG.garden.tree) : Prop :=
  (LG.layer a < p ∨ a.1.2 ∈ (LG.garden.tree a.1.1).leaves) ∧ a.1.2 ≠ [] ∧ LG.parentLayer p a = p

end LayeredGarden
end WaveTurbulence
