/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.Contract
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! # Exact finite coordinate blocks of the full-vine contract -/

public section
namespace WaveTurbulence.Vine.Param
open VineParamContract

/-- Reference, x block, y block and optional three-dimensional core. -/
abbrev ContractCoordinateTree {X : VineType} (A : Shape X) :=
  ((Fin 1 ⊕ Fin A.m) ⊕ Fin A.m) ⊕ Fin (if X.IsBad then 0 else 3)

/-- The contract's consecutive coordinate blocks, with no cardinality choice. -/
@[expose] def contractCoordinateEquiv {X : VineType} (A : Shape X) :
    ContractCoordinateTree A ≃ Fin A.n :=
  ((Equiv.sumCongr
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv)
      (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (by unfold Shape.n; omega))

/-- The initial block is exactly the designated physical reference. -/
theorem contractCoordinateEquiv_reference {X : VineType} (A : Shape X) :
    contractCoordinateEquiv A (.inl (.inl (.inl 0)))=A.x0 := by
  apply Fin.ext
  rfl

/-- The x block agrees exactly with Shape.xSlot. -/
theorem contractCoordinateEquiv_x {X : VineType} (A : Shape X) (j : Fin A.m) :
    contractCoordinateEquiv A (.inl (.inl (.inr j)))=A.xSlot j := by
  apply Fin.ext
  change 1+j.1=j.1+1
  omega

/-- The y block agrees exactly with Shape.ySlot. -/
theorem contractCoordinateEquiv_y {X : VineType} (A : Shape X) (j : Fin A.m) :
    contractCoordinateEquiv A (.inl (.inr j))=A.ySlot j := by
  apply Fin.ext
  change (1+A.m)+j.1=A.m+1+j.1
  omega

/-- The last block is the complete normal-vine core. -/
theorem contractCoordinateEquiv_core {X : VineType} (A : Shape X) (hn : X.IsBad=false) (j : Fin 3) :
    contractCoordinateEquiv A (.inr ⟨j.1,by simpa only [hn,Bool.false_eq_true,ite_false] using j.2⟩)=A.uSlot hn j := by
  apply Fin.ext
  change ((1+A.m)+A.m)+j.1=2*A.m+1+j.1
  omega

/-- Appending one allowed rung changes m by one and retains all source
endpoint conventions, including the m=1 type-II base case. -/
@[expose] def insertedShape {X : VineType} (A : Shape X) (hX : X ≠ .I) : Shape X where
  m := A.m+1
  typeI := fun h => (hX h).elim
  typeII := fun h => by have := A.typeII h; omega

/-- Gather the two added paired coordinates, retaining the original four
coordinate blocks and their order. -/
@[expose] def gatherAddedPair (A B C D U W : Type*) :
    (((A ⊕ (B ⊕ U)) ⊕ (C ⊕ W)) ⊕ D) ≃ ((((A ⊕ B) ⊕ C) ⊕ D) ⊕ (U ⊕ W)) where
  toFun
    | .inl (.inl (.inl a)) => .inl (.inl (.inl (.inl a)))
    | .inl (.inl (.inr (.inl b))) => .inl (.inl (.inl (.inr b)))
    | .inl (.inl (.inr (.inr u))) => .inr (.inl u)
    | .inl (.inr (.inl c)) => .inl (.inl (.inr c))
    | .inl (.inr (.inr w)) => .inr (.inr w)
    | .inr d => .inl (.inr d)
  invFun
    | .inl (.inl (.inl (.inl a))) => .inl (.inl (.inl a))
    | .inl (.inl (.inl (.inr b))) => .inl (.inl (.inr (.inl b)))
    | .inl (.inl (.inr c)) => .inl (.inr (.inl c))
    | .inl (.inr d) => .inr d
    | .inr (.inl u) => .inl (.inl (.inr (.inr u)))
    | .inr (.inr w) => .inl (.inr (.inr w))
  left_inv := by rintro (((a | (b | u)) | (c | w)) | d) <;> rfl
  right_inv := by rintro ((((a | b) | c) | d) | (u | w)) <;> rfl

/-- The source coordinate tree with its two appended paired variables. -/
@[expose] def slotInsertionTreeEquiv {X : VineType} (A : Shape X) (hX : X ≠ .I) :
    ContractCoordinateTree (insertedShape A hX) ≃ (Fin A.n ⊕ Fin 2) :=
  (Equiv.sumCongr
      (Equiv.sumCongr (Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv.symm)
        finSumFinEquiv.symm) (Equiv.refl _)).trans
      ((gatherAddedPair _ _ _ _ _ _).trans
        (Equiv.sumCongr (contractCoordinateEquiv A) finSumFinEquiv))

/-- Exact reindexing after one rung: all old coordinates plus the new x/y
pair, while the public contract keeps its consecutive x and y blocks. -/
@[expose] def slotInsertionEquiv {X : VineType} (A : Shape X) (hX : X ≠ .I) :
    Fin (insertedShape A hX).n ≃ (Fin A.n ⊕ Fin 2) :=
  (contractCoordinateEquiv (insertedShape A hX)).symm.trans (slotInsertionTreeEquiv A hX)

/-- Explicit cancellation of the public coordinate flattening. -/
theorem slotInsertionEquiv_on_tree {X : VineType} (A : Shape X) (hX : X ≠ .I)
    (q : ContractCoordinateTree (insertedShape A hX)) :
    slotInsertionEquiv A hX (contractCoordinateEquiv (insertedShape A hX) q)=
      slotInsertionTreeEquiv A hX q := by
  change slotInsertionTreeEquiv A hX
    ((contractCoordinateEquiv (insertedShape A hX)).symm
      (contractCoordinateEquiv (insertedShape A hX) q))=_
  rw [Equiv.symm_apply_apply]

end WaveTurbulence.Vine.Param
