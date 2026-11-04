/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# TTree.pre

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `deftree`, L625–L631. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace TTree

/-- Prefix every path of a set by a first step `i`. -/
def pre (i : Fin 3) (S : Finset Path) : Finset Path := S.image (List.cons i)

end TTree
end WaveTurbulence
