/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.SumintShape

/-!
# SumintShape.TVar

Wave B tier B1 (WaveB1-Sumint.lean), source: (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace SumintShape

variable (S : SumintShape)

/-- The input time variables: `t_jⁱ` (`j ≤ m_i`), `s_jⁱ` (`1 ≤ j ≤ m_i`, stored as `j - 1`),
`τ_jⁱ` (`i ∈ Nor`). -/
abbrev TVar : Type :=
  (Σ i : Fin S.I, Fin (S.m i + 1)) ⊕ (Σ i : Fin S.I, Fin (S.m i)) ⊕
    (Σ _ : {i : Fin S.I // S.nor i = true}, Fin 3)

end SumintShape
end WaveTurbulence
