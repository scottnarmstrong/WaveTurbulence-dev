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
# MiniTreeCode.red

Wave B tier B2 (WaveB2-Regular.lean), source: (file) WAVE-B v2 §2.7; L826–L829; L848–L850. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

namespace MiniTreeCode

/-- The red pair `(ρ-slot, ν-slot)`: the pair containing the leftmost leaf child of `ρ`. -/
def red (m : MiniTreeCode) : Fin 3 × Fin 3 :=
  (![![(1, 2), (1, 0)], ![(0, 0), (0, 2)], ![(0, 1), (0, 1)]] : Fin 3 → Fin 2 → Fin 3 × Fin 3) m.c m.b

end MiniTreeCode
end WaveTurbulence
