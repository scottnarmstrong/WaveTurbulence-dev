/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.MiniTreeCode
public import WaveTurbulence.Frozen.Defs.TTree

/-!
# MiniTreeCode.lone

Wave B tier B2 (WaveB2-Regular.lean), source: WAVE-B §3.2. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

namespace MiniTreeCode

/-- The slot of the lone leaf under `ν` (table of WAVE-B §3.2): codes `10, 11, 20, 21, 30, 31` give
`L, R, M, M, R, L`. -/
def lone (m : MiniTreeCode) : Fin 3 := (![![0, 2], ![1, 1], ![2, 0]] : Fin 3 → Fin 2 → Fin 3) m.c m.b

end MiniTreeCode
end WaveTurbulence
