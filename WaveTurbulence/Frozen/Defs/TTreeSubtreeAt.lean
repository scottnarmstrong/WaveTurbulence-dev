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
# TTree.subtreeAt

Wave B tier B2 (WaveB2-Regular.lean), source: (section) T Def `defreg`, L826–L829. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- The subtree at path `p` (`•` if `p` is not a node; only used at nodes). -/
def TTree.subtreeAt : TTree → Path → TTree
  | T, [] => T
  | .leaf, _ :: _ => .leaf
  | .node l m r, i :: p => (![l, m, r] i).subtreeAt p

end WaveTurbulence
