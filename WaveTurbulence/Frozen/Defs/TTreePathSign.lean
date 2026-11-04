/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# TTree.pathSign

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `deftree`, L625–L631. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace TTree

/-- The sign `ζ_𝔫` of the node at path `p` in a tree of sign `ζ`: children of a node of sign `ζ'`
have signs `(ζ', -ζ', ζ')`, so `ζ_𝔫 = ζ (-1)^{#mid steps}`. -/
def pathSign (ζ : ℤˣ) (p : Path) : ℤˣ := ζ * (-1) ^ (p.count 1)

end TTree
end WaveTurbulence
