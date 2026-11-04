/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchToNode
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeIsDesc
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InstDecidableIsDesc
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch
public import WaveTurbulence.Frozen.Defs.LayeredGarden

/-!
# LayeredGarden.topCountBelow

Wave B tier B1 (WaveB1-Flower.lean), source: T L2290. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The number of layer-`p` branching nodes below `a` (the "order" of T L2290). -/
def topCountBelow (p : ℕ) (a : GNode LG.garden.tree) : ℕ :=
  (Finset.univ.filter fun b : GBranch LG.garden.tree =>
    a.IsDesc b.toNode ∧ LG.layer b.toNode = p).card

end LayeredGarden
end WaveTurbulence
