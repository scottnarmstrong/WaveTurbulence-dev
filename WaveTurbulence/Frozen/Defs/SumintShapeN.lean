/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.SumintShape

/-!
# SumintShape.n

Wave B tier B1 (WaveB1-Sumint.lean), source: (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace SumintShape

variable (S : SumintShape)

/-- `n_i = 2m_i + 1 + 3·1_Nor(i)`. -/
def n (i : Fin S.I) : ℕ := 2 * S.m i + 1 + if S.nor i then 3 else 0

end SumintShape
end WaveTurbulence
