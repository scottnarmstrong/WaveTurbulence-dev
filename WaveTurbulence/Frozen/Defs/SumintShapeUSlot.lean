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
# SumintShape.uSlot

Wave B tier B1 (WaveB1-Sumint.lean), source: (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace SumintShape

variable (S : SumintShape)

/-- The slot of `u_cⁱ` (`i ∈ Nor`, `c = 0,1,2` for `u₁, u₂, u₃`). -/
def uSlot (i : Fin S.I) (h : S.nor i = true) (c : Fin 3) : S.VIdx :=
  ⟨i, ⟨2 * S.m i + 1 + c, by unfold n; simp only [h, ite_true]; omega⟩⟩

end SumintShape
end WaveTurbulence
