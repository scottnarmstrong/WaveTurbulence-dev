/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# GBranch

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `defgarden`, L632–L638. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Forest

open TTree
variable {w : ℕ} (tree : Fin w → TTree)

/-- The branching nodes `𝒩 = 𝒩₁ ∪ ⋯ ∪ 𝒩_w` of a forest. -/
def GBranch : Type := {a : Fin w × Path // a.2 ∈ (tree a.1).branching}

end Forest
end WaveTurbulence
