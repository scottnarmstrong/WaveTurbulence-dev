/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.SumintShape
public import WaveTurbulence.Frozen.Defs.SumintShapeN
public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx

/-!
# SumintShape.ySlot

Wave B tier B1 (WaveB1-Sumint.lean), source: (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace SumintShape

variable (S : SumintShape)

/-- The slot of `y_jⁱ`. -/
def ySlot (i : Fin S.I) (j : Fin (S.m i)) : S.VIdx := ⟨i, ⟨S.m i + 1 + j, by unfold n; omega⟩⟩

end SumintShape
end WaveTurbulence
