/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# TTree

Wave B tier B1 (WaveB1-Core.lean), source: T Def `deftree`; DH21 Def 2.1. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- A ternary tree: a leaf, or a branching node with left, mid and right subtrees
(T Def `deftree`; DH21 Def 2.1). The trivial tree `•` is `leaf`. -/
inductive TTree : Type
  | leaf : TTree
  | node (l m r : TTree) : TTree

end WaveTurbulence
