/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockContraction
import Mathlib.Tactic

/-! # Expanding the merged vertex to its distinguished upper joint -/

public section
namespace WaveTurbulence.Mole
variable {V : Type*} [DecidableEq V] (S : Finset V) (a : V) (ha : a ∈ S)

/-- One retained representative for the merged point, and every old outside point. -/
@[expose] def contractionPointEquiv : ContractVertex S ≃ {v : V // v ∉ S ∨ v = a} where
  toFun
    | none => ⟨a,Or.inr rfl⟩
    | some v => ⟨v.1,Or.inl v.2⟩
  invFun v := if h : v.1 ∉ S then some ⟨v.1,h⟩ else none
  left_inv v := by
    cases v with
    | none => exact dite_eq_right (not_not.mpr ha)
    | some v => exact dite_eq_left v.2
  right_inv v := by
    dsimp only
    by_cases h : v.1 ∉ S
    · rw [dite_eq_left h]
    · have he : v.1 = a := v.2.resolve_left h
      rw [dite_eq_right h]
      exact Subtype.ext he.symm

end WaveTurbulence.Mole
