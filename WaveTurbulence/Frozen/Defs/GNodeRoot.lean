/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.TTreePre

/-!
# GNode.root

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

variable (tree) in
/-- The root `𝔯_j` of the `j`-th tree. -/
def GNode.root (j : Fin w) : GNode tree :=
  ⟨(j, []), by
    show ([] : TTree.Path) ∈ (tree j).nodes
    rcases tree j with _ | ⟨l, m, r⟩ <;> simp [TTree.nodes]⟩

end Forest
end WaveTurbulence
