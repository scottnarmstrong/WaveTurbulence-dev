/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeIsDesc
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# GNode.Incomparable

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

/-- Two nodes are incomparable if neither is a descendant of the other. -/
def GNode.Incomparable (a a' : GNode tree) : Prop := ¬ a.IsDesc a' ∧ ¬ a'.IsDesc a

end Forest
end WaveTurbulence
