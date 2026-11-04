/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GBranchToNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# LayeredGarden.topOrder

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `defgtr`, L731–L732. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The order of the top tree `𝒯_j^p`: the number of branching nodes of `𝒯_j` in layer `p`. -/
def topOrder (p : ℕ) (j : Fin w) : ℕ :=
  (Finset.univ.filter fun b : GBranch LG.garden.tree => b.1.1 = j ∧ LG.layer b.toNode = p).card

end LayeredGarden
end WaveTurbulence
