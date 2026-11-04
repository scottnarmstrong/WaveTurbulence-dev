/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.PiCharacter

/-!
# Literal real exponents and scalar amplitudes of the source phase

These definitions separate the finite products in the exact owner-corrected
snapshot datum. They retain every time parameter and affine r term. The
case-(c) amplitude is kept multiplicative, so no division by a potentially
zero phase factor is introduced.
-/

public section

open Finset

namespace WaveTurbulence.Sumint

/-- The exact case-(c) scalar factor in one source block. -/
@[expose] noncomputable def caseCFactor {d : ℕ} (D : SumintDatum d) (η : ℝ)
    (τ : D.S.TVar → ℝ) (i : Fin D.S.I) : ℂ :=
  if h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i then
    ((|τ (.inl ⟨i,⟨1,by omega⟩⟩)-τ (.inr (.inl ⟨i,⟨0,h.2.2⟩⟩))|^(1-3*η) : ℝ) : ℂ)
  else 1

/-- The full positive scalar amplitude in the source phase. -/
@[expose] noncomputable def caseCAmplitude {d : ℕ} (D : SumintDatum d) (η : ℝ)
    (τ : D.S.TVar → ℝ) : ℂ := ∏ i, caseCFactor D η τ i

/-- The exact first-block real phase exponent, before subtracting its zero-input value. -/
@[expose] noncomputable def firstPhaseExponent {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) (i : Fin D.S.I) : ℝ :=
  let c := δ*L^(2*γ)
  let X := fun v => latticePoint L (x v)
  (∑ j : Fin (D.S.m i), c*(τ (.inl ⟨i,j.succ⟩)-τ (.inr (.inl ⟨i,j⟩))) *
    inner ℝ (X (D.S.xSlot i j)) (X (D.S.ySlot i j))) +
  c*(τ (.inl ⟨i,0⟩)-t)*inner ℝ r (X (D.S.x0Slot i)) +
  (∑ j : Fin (D.S.m i), c*(τ (.inl ⟨i,j.succ⟩)-t)*inner ℝ r
    ((D.ζc i j 0 : ℝ) • X (D.S.xSlot i j)+(D.ζc i j 1 : ℝ) • X (D.S.ySlot i j)+
      (D.ζc i j 2 : ℝ) • r)) +
  (∑ j : Fin (D.S.m i+1), D.param (.inl ⟨i,j⟩)*τ (.inl ⟨i,j⟩)) +
  ∑ j : Fin (D.S.m i), D.param (.inr (.inl ⟨i,j⟩))*τ (.inr (.inl ⟨i,j⟩))

/-- The exact real exponent of a normal block, including all three time parameters. -/
@[expose] noncomputable def normalPhaseExponent {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) : ℝ :=
  let c := δ*L^(2*γ)
  let u := fun j : Fin 3 => latticePoint L (x (D.S.uSlot i.1 i.2 j))
  let τ' := fun j : Fin 3 => τ (.inr (.inr ⟨i,j⟩))
  c*(τ' 0-τ' 2)*inner ℝ (u 0) (u 1) +
  c*(τ' 1-τ' 2)*(if D.Λsel i.1 then inner ℝ (u 0) (u 2) else inner ℝ (u 2) (u 0+u 1-u 2)) +
  c*(τ' 2-t)*inner ℝ r ((D.ξc i.1 0 : ℝ) • u 0+(D.ξc i.1 1 : ℝ) • u 1+
    (D.ξc i.1 2 : ℝ) • u 2+(D.ξc i.1 3 : ℝ) • r) +
  ∑ j : Fin 3, D.param (.inr (.inr ⟨i,j⟩))*τ' j

/-- The sum of all literal real exponents in the source phase. -/
@[expose] noncomputable def fullPhaseExponent {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) : ℝ :=
  (∑ i, firstPhaseExponent D L γ δ x r t τ i) + ∑ i, normalPhaseExponent D L γ δ x r t τ i

/-- The first source product factor, with its literal scalar amplitude. -/
@[expose] noncomputable def firstPhaseFactor {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) (i : Fin D.S.I) : ℂ :=
  let c := δ*L^(2*γ)
  let X := fun v => latticePoint L (x v)
  (∏ j : Fin (D.S.m i), piCharacter (c*(τ (.inl ⟨i,j.succ⟩)-τ (.inr (.inl ⟨i,j⟩))) *
    inner ℝ (X (D.S.xSlot i j)) (X (D.S.ySlot i j)))) *
  piCharacter (c*(τ (.inl ⟨i,0⟩)-t)*inner ℝ r (X (D.S.x0Slot i))) *
  (∏ j : Fin (D.S.m i), piCharacter (c*(τ (.inl ⟨i,j.succ⟩)-t)*inner ℝ r
    ((D.ζc i j 0 : ℝ) • X (D.S.xSlot i j)+(D.ζc i j 1 : ℝ) • X (D.S.ySlot i j)+
      (D.ζc i j 2 : ℝ) • r))) *
  (∏ j : Fin (D.S.m i+1), piCharacter (D.param (.inl ⟨i,j⟩)*τ (.inl ⟨i,j⟩))) *
  (∏ j : Fin (D.S.m i), piCharacter (D.param (.inr (.inl ⟨i,j⟩))*τ (.inr (.inl ⟨i,j⟩)))) *
  caseCFactor D η τ i

/-- The second source product factor for a normal block. -/
@[expose] noncomputable def normalPhaseFactor {d : ℕ} (D : SumintDatum d) (L γ δ : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) : ℂ :=
  let c := δ*L^(2*γ)
  let u := fun j : Fin 3 => latticePoint L (x (D.S.uSlot i.1 i.2 j))
  let τ' := fun j : Fin 3 => τ (.inr (.inr ⟨i,j⟩))
  piCharacter (c*(τ' 0-τ' 2)*inner ℝ (u 0) (u 1)) *
  piCharacter (c*(τ' 1-τ' 2)*(if D.Λsel i.1 then inner ℝ (u 0) (u 2) else inner ℝ (u 2) (u 0+u 1-u 2))) *
  piCharacter (c*(τ' 2-t)*inner ℝ r ((D.ξc i.1 0 : ℝ) • u 0+(D.ξc i.1 1 : ℝ) • u 1+
    (D.ξc i.1 2 : ℝ) • u 2+(D.ξc i.1 3 : ℝ) • r)) *
  ∏ j : Fin 3, piCharacter (D.param (.inr (.inr ⟨i,j⟩))*τ' j)

/-- These are literally the two separately delimited products in the corrected source datum. -/
theorem phase_eq_factor_products {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    D.phase L γ δ η x r t τ = (∏ i, firstPhaseFactor D L γ δ η x r t τ i) *
      ∏ i, normalPhaseFactor D L γ δ x r t τ i := rfl

end WaveTurbulence.Sumint
