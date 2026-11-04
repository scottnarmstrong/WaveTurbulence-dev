/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.SumintShape
public import WaveTurbulence.Frozen.Defs.SumintShapeN

/-!
# SumintShape.VIdx

Wave B tier B1 (WaveB1-Sumint.lean), source: (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace SumintShape

variable (S : SumintShape)

/-- The input vector variables `x = (x₀ⁱ, x_jⁱ, y_jⁱ, u_jⁱ)` (and the alternative variables
`k_jⁱ, ℓ_jⁱ`, indexed the same way). -/
abbrev VIdx : Type := Σ i : Fin S.I, Fin (S.n i)

end SumintShape
end WaveTurbulence
