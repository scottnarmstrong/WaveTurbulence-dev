/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamContractCoordinates
import Mathlib.Tactic

/-! # Actual included-atom bijection after adding two fresh rung atoms -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V : Type*} [DecidableEq V]

/-- Deleting the old upper joint leaves all old included atoms and both
fresh rung atoms. This is an explicit bijection of actual atom values. -/
@[expose] def excludedSumEquiv (a : V) :
    {v : V ⊕ Fin 2 // v ≠ .inl a} ≃ ({v : V // v ≠ a} ⊕ Fin 2) where
  toFun
    | ⟨.inl v,hv⟩ => .inl ⟨v,fun h => hv (congrArg Sum.inl h)⟩
    | ⟨.inr j,_⟩ => .inr j
  invFun
    | .inl ⟨v,hv⟩ => ⟨.inl v,fun h => hv (Sum.inl.inj h)⟩
    | .inr j => ⟨.inr j,by simp⟩
  left_inv := by rintro ⟨(v | j),hv⟩ <;> rfl
  right_inv := by rintro (⟨v,hv⟩ | j) <;> rfl

/-- Finset deletion of a universal atom group agrees with literal inequality. -/
@[expose] def erasedUnivEquiv [Fintype V] (a : V) :
    ↥((univ : Finset V).erase a) ≃ {v : V // v ≠ a} :=
  Equiv.subtypeEquivRight (fun v => by simp only [mem_erase,mem_univ,and_true])

/-- The new included atom group is the old included group plus exactly the
actual two fresh vertices. -/
@[expose] def erasedUnivSumEquiv [Fintype V] (a : V) :
    ↥((univ : Finset (V ⊕ Fin 2)).erase (.inl a)) ≃ (↥((univ : Finset V).erase a) ⊕ Fin 2) :=
  (erasedUnivEquiv (Sum.inl a : V ⊕ Fin 2)).trans ((excludedSumEquiv a).trans
    (Equiv.sumCongr (erasedUnivEquiv a).symm (Equiv.refl _)))

/-- The coordinate insertion map retains the designated physical reference. -/
theorem slotInsertionEquiv_reference {X : VineType} (A : VineParamContract.Shape X) (hX : X ≠ .I) :
    slotInsertionEquiv A hX (insertedShape A hX).x0=Sum.inl A.x0 := by
  rw [← contractCoordinateEquiv_reference (insertedShape A hX)]
  simp only [slotInsertionEquiv]
  change Sum.inl (contractCoordinateEquiv A (.inl (.inl (.inl 0))))=Sum.inl A.x0
  rw [contractCoordinateEquiv_reference]

/-- An existing actual included-atom indexing lifts to the precise enlarged
contract coordinate blocks. No finite-cardinality choice is used. -/
@[expose] def insertedAtomEquiv [Fintype V] {X : VineType} (A : VineParamContract.Shape X)
    (hX : X ≠ .I) (a : V) (old : Fin A.n ≃ ↥((univ : Finset V).erase a)) :
    Fin (insertedShape A hX).n ≃ ↥((univ : Finset (V ⊕ Fin 2)).erase (.inl a)) :=
  (slotInsertionEquiv A hX).trans
    ((Equiv.sumCongr old (Equiv.refl _)).trans (erasedUnivSumEquiv a).symm)

end WaveTurbulence.Vine.Param
