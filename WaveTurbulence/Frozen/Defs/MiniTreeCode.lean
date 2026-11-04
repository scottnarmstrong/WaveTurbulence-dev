/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# MiniTreeCode

Wave B tier B2 (WaveB2-Regular.lean), source: T Def `defreg`; WAVE-B §3.2. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- The code of a mini-tree (T Def `defreg`, Figure `MiniTree.png`; WAVE-B §3.2, figure-defs §5): a
root `ρ` with a branching child `ν` at slot `c` (`0, 1, 2` = L, M, R; first code digit `c + 1`) and
second digit `b`. -/
structure MiniTreeCode where
  /-- the slot of the inner node `ν` under the root `ρ` -/
  c : Fin 3
  /-- the second code digit -/
  b : Fin 2

end WaveTurbulence
