/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedAtoms
import Mathlib.Tactic

/-! # Exact nonreference coordinate partition for physical-origin induction -/

public section
namespace WaveTurbulence.Vine.Param
open VineParamContract

/-- Removing the new reference leaves precisely the old nonreference slots
and the two appended internal differences, without a dummy reference branch. -/
@[expose] def nonreferenceInsertionEquiv {X : VineType} (A : Shape X) (hX : X ≠ .I) :
    {i : Fin (insertedShape A hX).n // i ≠ (insertedShape A hX).x0} ≃
      ({j : Fin A.n // j ≠ A.x0} ⊕ Fin 2) :=
  (Equiv.subtypeEquiv (slotInsertionEquiv A hX) (fun i => by
    constructor
    · intro hn he
      apply hn
      apply (slotInsertionEquiv A hX).injective
      exact he.trans (slotInsertionEquiv_reference A hX).symm
    · intro hn he
      apply hn
      rw [he,slotInsertionEquiv_reference])).trans (excludedSumEquiv A.x0)

/-- Forgetting only the deletion proof recovers exactly the original
contract coordinate insertion map. -/
theorem nonreferenceInsertionEquiv_value {X : VineType} (A : Shape X) (hX : X ≠ .I)
    (i : {i : Fin (insertedShape A hX).n // i ≠ (insertedShape A hX).x0}) :
    Sum.map Subtype.val id (nonreferenceInsertionEquiv A hX i)=slotInsertionEquiv A hX i.1 := by
  cases h : slotInsertionEquiv A hX i.1 with
  | inl j => simp [nonreferenceInsertionEquiv,Equiv.subtypeEquiv,excludedSumEquiv,h]
  | inr j => simp [nonreferenceInsertionEquiv,Equiv.subtypeEquiv,excludedSumEquiv,h]

end WaveTurbulence.Vine.Param
