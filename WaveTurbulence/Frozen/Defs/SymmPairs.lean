/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# symmPairs

Wave B tier B2 (WaveB2-Regular.lean), source: (section) T Def `defreg`, L826–L829. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- A list of pairs together with the swapped pairs (pairs read as unordered). -/
def symmPairs {α : Type*} (P : List (α × α)) : List (α × α) := P ++ P.map Prod.swap

end WaveTurbulence
