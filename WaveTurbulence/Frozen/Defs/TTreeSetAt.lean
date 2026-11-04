/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# TTree.setAt

Wave B tier B2 (WaveB2-Regular.lean), source: (section) T Def `defreg`, L826–L829. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- Replace the subtree at path `p` by `S` (unchanged if `p` is not a node; only used at nodes). -/
def TTree.setAt : TTree → Path → TTree → TTree
  | _, [], S => S
  | .leaf, _ :: _, _ => .leaf
  | .node l m r, i :: p, S =>
    .node (if i = 0 then l.setAt p S else l) (if i = 1 then m.setAt p S else m)
      (if i = 2 then r.setAt p S else r)

end WaveTurbulence
