/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.SumintDatum
public import WaveTurbulence.Frozen.Defs.SumintShape
public import WaveTurbulence.Frozen.Defs.SumintShapeTVar

/-!
# SumintDatum.timeDom

Wave B tier B1 (WaveB1-Sumint.lean), source: T L1612–L1613. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace SumintDatum

variable {d : ℕ} (D : SumintDatum d)

/-- The input time domain `𝒟(t, t', t'')` (T L1612–L1613): unit intervals, all `< t`, `t₀¹ >
max(t', t'')`, and the order constraints. Requires `I ≥ 1`. -/
def timeDom (hI : 0 < D.S.I) (t t' t'' : ℝ) : Set (D.S.TVar → ℝ) :=
  {τ | (∀ v, (D.q v : ℝ) ≤ τ v ∧ τ v ≤ D.q v + 1 ∧ τ v < t) ∧
    max t' t'' < τ (.inl ⟨⟨0, hI⟩, 0⟩) ∧ ∀ c ∈ D.constraints, τ c.1 < τ c.2}

end SumintDatum
end WaveTurbulence
