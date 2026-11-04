/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# TTree.order

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `deftree`, L625–L631. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace TTree

/-- The order `n(𝒯) = |𝒩|`, the number of branching nodes. -/
def order : TTree → ℕ
  | leaf => 0
  | node l m r => l.order + m.order + r.order + 1

end TTree
end WaveTurbulence
