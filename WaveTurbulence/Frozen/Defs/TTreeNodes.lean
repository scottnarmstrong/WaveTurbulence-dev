/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.TTreePre

/-!
# TTree.nodes

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `deftree`, L625–L631. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace TTree

/-- All node addresses. -/
def nodes : TTree → Finset Path
  | leaf => {[]}
  | node l m r => insert [] (pre 0 l.nodes ∪ pre 1 m.nodes ∪ pre 2 r.nodes)

end TTree
end WaveTurbulence
