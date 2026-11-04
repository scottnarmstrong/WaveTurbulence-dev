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

/-!
# GNode.IsDesc

Wave B tier B1 (WaveB1-Core.lean), source: T L627. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Forest

open TTree
variable {w : ℕ} (tree : Fin w → TTree)
variable {tree}

/-- `IsDesc a a'`: the node `a'` is a descendant of `a` (`a' = a` allowed, T L627). -/
def GNode.IsDesc (a a' : GNode tree) : Prop := a.1.1 = a'.1.1 ∧ a.1.2 <+: a'.1.2

end Forest
end WaveTurbulence
