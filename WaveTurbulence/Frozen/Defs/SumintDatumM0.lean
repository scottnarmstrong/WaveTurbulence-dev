/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.SumintDatum
public import WaveTurbulence.Frozen.Defs.SumintShape

/-!
# SumintDatum.M₀

Wave B tier B1 (WaveB1-Sumint.lean), source: T L1622–L1623. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace SumintDatum

variable {d : ℕ} (D : SumintDatum d)

/-- `M₀`: the number of pairs `(t_jⁱ, s_jⁱ)` in different unit intervals, plus the number of `i ∈ Nor`
whose `τ₁ⁱ, τ₂ⁱ, τ₃ⁱ` are not in one unit interval (T L1622–L1623, "`i ∈ A`" read as `i ∈ Nor`). -/
def M₀ : ℕ :=
  (Finset.univ.filter fun p : Σ i : Fin D.S.I, Fin (D.S.m i) =>
      D.q (.inl ⟨p.1, p.2.succ⟩) ≠ D.q (.inr (.inl ⟨p.1, p.2⟩))).card +
    (Finset.univ.filter fun i : {i : Fin D.S.I // D.S.nor i = true} =>
      ¬ (D.q (.inr (.inr ⟨i, 0⟩)) = D.q (.inr (.inr ⟨i, 1⟩)) ∧
        D.q (.inr (.inr ⟨i, 1⟩)) = D.q (.inr (.inr ⟨i, 2⟩)))).card

end SumintDatum
end WaveTurbulence
