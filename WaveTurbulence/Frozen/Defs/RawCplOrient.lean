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
# RawCpl.orient

Wave B tier B2 (WaveB2-Regular.lean), source: (section) T Def `defreg`, L826–L829. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

namespace RawCpl

/-- The oriented pair `(+ leaf, - leaf)` from a leaf `x` of sign `sx` and its partner `y`. -/
def orient (x : Fin 2 × Path) (sx : ℤˣ) (y : Fin 2 × Path) : (Fin 2 × Path) × (Fin 2 × Path) :=
  if sx = 1 then (x, y) else (y, x)

end RawCpl
end WaveTurbulence
