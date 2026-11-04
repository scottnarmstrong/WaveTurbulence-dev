/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# TTree.decEq

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `deftree`, L625–L631. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-- Decidable equality of ternary trees (structural recursion). -/
def TTree.decEq : (a b : TTree) → Decidable (a = b)
  | .leaf, .leaf => isTrue rfl
  | .leaf, .node .. => isFalse fun h => TTree.noConfusion h
  | .node .., .leaf => isFalse fun h => TTree.noConfusion h
  | .node l m r, .node l' m' r' =>
    match TTree.decEq l l', TTree.decEq m m', TTree.decEq r r' with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse h, _, _ => isFalse fun e => h (TTree.node.inj e).1
    | isTrue _, isFalse h, _ => isFalse fun e => h (TTree.node.inj e).2.1
    | isTrue _, isTrue _, isFalse h => isFalse fun e => h (TTree.node.inj e).2.2

end WaveTurbulence
