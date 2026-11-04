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
# RawCpl.relocate

Wave B tier B2 (WaveB2-Regular.lean), source: (section) T Def `defreg`, L826–L829. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

namespace RawCpl

/-- Relocate an address below `a` to below `a ++ [c, l]` (the old subtree is re-attached at the lone
leaf of the new mini-tree). -/
def relocate (a : Fin 2 × Path) (c l : Fin 3) (z : Fin 2 × Path) : Fin 2 × Path :=
  if z.1 = a.1 ∧ a.2 <+: z.2 then (z.1, a.2 ++ [c, l] ++ z.2.drop a.2.length) else z

end RawCpl
end WaveTurbulence
