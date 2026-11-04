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
public import WaveTurbulence.Frozen.Defs.SumintShapeTVar
public import WaveTurbulence.Frozen.Defs.SumintShapeUSlot
public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx
public import WaveTurbulence.Frozen.Defs.SumintShapeX0Slot
public import WaveTurbulence.Frozen.Defs.SumintShapeXSlot
public import WaveTurbulence.Frozen.Defs.SumintShapeYSlot

/-!
# SumintDatum.phase

Wave B tier B1 (WaveB1-Sumint.lean), source: (file) T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

namespace SumintDatum

variable {d : ℕ} (D : SumintDatum d)

/-- The phase of (sumintI1) at input vectors `x` and input times `τ`, including the extra factors
`|t₁ⁱ - s₁ⁱ|^{1-3η}` of the bad case (c). -/
noncomputable def phase (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) : ℂ :=
  let c := δ * L ^ (2 * γ)
  let X : D.S.VIdx → Mom d := fun v => latticePoint L (x v)
  let e (θ : ℝ) : ℂ := Complex.exp ((Real.pi * θ : ℝ) * Complex.I)
  (∏ i, ((∏ j : Fin (D.S.m i), e (c * (τ (.inl ⟨i, j.succ⟩) - τ (.inr (.inl ⟨i, j⟩))) *
        inner ℝ (X (D.S.xSlot i j)) (X (D.S.ySlot i j)))) *
      e (c * (τ (.inl ⟨i, 0⟩) - t) * inner ℝ r (X (D.S.x0Slot i))) *
      (∏ j : Fin (D.S.m i), e (c * (τ (.inl ⟨i, j.succ⟩) - t) * inner ℝ r
        ((D.ζc i j 0 : ℝ) • X (D.S.xSlot i j) + (D.ζc i j 1 : ℝ) • X (D.S.ySlot i j) +
          (D.ζc i j 2 : ℝ) • r))) *
      (∏ j : Fin (D.S.m i + 1), e (D.param (.inl ⟨i, j⟩) * τ (.inl ⟨i, j⟩))) *
      (∏ j : Fin (D.S.m i), e (D.param (.inr (.inl ⟨i, j⟩)) * τ (.inr (.inl ⟨i, j⟩)))) *
      (if h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i then
        ((|τ (.inl ⟨i, ⟨1, by omega⟩⟩) - τ (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩))| ^ (1 - 3 * η) : ℝ) : ℂ)
      else 1))) *
  ∏ i : {i : Fin D.S.I // D.S.nor i = true},
    let u (c' : Fin 3) := X (D.S.uSlot i.1 i.2 c')
    let τ' (c' : Fin 3) := τ (.inr (.inr ⟨i, c'⟩))
    e (c * (τ' 0 - τ' 2) * inner ℝ (u 0) (u 1)) *
      e (c * (τ' 1 - τ' 2) *
        (if D.Λsel i.1 then inner ℝ (u 0) (u 2) else inner ℝ (u 2) (u 0 + u 1 - u 2))) *
      e (c * (τ' 2 - t) * inner ℝ r ((D.ξc i.1 0 : ℝ) • u 0 + (D.ξc i.1 1 : ℝ) • u 1 +
        (D.ξc i.1 2 : ℝ) • u 2 + (D.ξc i.1 3 : ℝ) • r)) *
      ∏ c', e (D.param (.inr (.inr ⟨i, c'⟩)) * τ' c')

end SumintDatum
end WaveTurbulence
