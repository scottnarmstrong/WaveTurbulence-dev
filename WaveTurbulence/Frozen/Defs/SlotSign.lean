/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# slotSign

Wave B tier B2 (WaveB2-Regular.lean), source: T L627. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- The sign of the child at slot `i` of a node of sign `ζ`: `(ζ, -ζ, ζ)` (T L627). -/
def slotSign (ζ : ℤˣ) (i : Fin 3) : ℤˣ := if i = 1 then -ζ else ζ

end WaveTurbulence
