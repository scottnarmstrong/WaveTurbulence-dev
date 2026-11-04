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
public import WaveTurbulence.Frozen.Defs.InstDecidableIsDesc
public import WaveTurbulence.Frozen.Defs.InstFintypeGBranch
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# GNode.orderBelow

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `defgarden`, L632–L638. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Forest

open TTree
variable {w : ℕ} (tree : Fin w → TTree)
variable {tree}

/-- The number of branching nodes of the subtree rooted at `a` (its order). -/
def GNode.orderBelow (a : GNode tree) : ℕ :=
  (Finset.univ.filter fun b : GBranch tree => a.IsDesc b.toNode).card

end Forest
end WaveTurbulence
