/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.SumintDatum
public import WaveTurbulence.Frozen.Defs.SumintShape
public import WaveTurbulence.Frozen.Defs.SumintShapeN
public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx

/-!
# SumintDatum.ℓVec

Wave B tier B1 (WaveB1-Sumint.lean), source: (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace SumintDatum

variable {d : ℕ} (D : SumintDatum d)

noncomputable def ℓVec (L : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (efgh : Fin 4 → Mom d) (v : D.S.VIdx) :
    Mom d :=
  ∑ v', (D.T₂ v v' : ℝ) • latticePoint L (x v') + ∑ c, (D.H₂ v c : ℝ) • efgh c

end SumintDatum
end WaveTurbulence
