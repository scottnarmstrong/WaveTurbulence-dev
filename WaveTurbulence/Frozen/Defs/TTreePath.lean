/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# TTree.Path

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `deftree`, L625–L631. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace TTree

/-- Node addresses: the path from the root, `0, 1, 2` = left, mid, right child. The children of
the node at `p` are `p ++ [0], p ++ [1], p ++ [2]`; the parent of `p ≠ []` is `p.dropLast`. -/
abbrev Path := List (Fin 3)

end TTree
end WaveTurbulence
