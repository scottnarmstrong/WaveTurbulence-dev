/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamInsertedAtoms
import Mathlib.Tactic

/-! # Contract slot formulas for appending one paired rung -/

public section
namespace WaveTurbulence.Vine.Param
open VineParamContract

/-- Every old x coordinate retains its original source slot. -/
theorem slotInsertionEquiv_old_x {X : VineType} (A : Shape X) (hX : X ≠ .I) (j : Fin A.m) :
    slotInsertionEquiv A hX ((insertedShape A hX).xSlot (Fin.castSucc j))=Sum.inl (A.xSlot j) := by
  rw [← contractCoordinateEquiv_x (insertedShape A hX) (Fin.castSucc j)]
  rw [slotInsertionEquiv_on_tree]
  change Sum.map (contractCoordinateEquiv A) finSumFinEquiv
    (gatherAddedPair (Fin 1) (Fin A.m) (Fin A.m) (Fin (if X.IsBad then 0 else 3)) (Fin 1) (Fin 1)
      (.inl (.inl (.inr (finSumFinEquiv.symm (Fin.castSucc j))))))=_
  rw [finSumFinEquiv_symm_apply_castSucc]
  change Sum.inl (contractCoordinateEquiv A (.inl (.inl (.inr j))))=_
  rw [contractCoordinateEquiv_x]

/-- Every old y coordinate retains its original source slot. -/
theorem slotInsertionEquiv_old_y {X : VineType} (A : Shape X) (hX : X ≠ .I) (j : Fin A.m) :
    slotInsertionEquiv A hX ((insertedShape A hX).ySlot (Fin.castSucc j))=Sum.inl (A.ySlot j) := by
  rw [← contractCoordinateEquiv_y (insertedShape A hX) (Fin.castSucc j)]
  rw [slotInsertionEquiv_on_tree]
  change Sum.map (contractCoordinateEquiv A) finSumFinEquiv
    (gatherAddedPair (Fin 1) (Fin A.m) (Fin A.m) (Fin (if X.IsBad then 0 else 3)) (Fin 1) (Fin 1)
      (.inl (.inr (finSumFinEquiv.symm (Fin.castSucc j)))))=_
  rw [finSumFinEquiv_symm_apply_castSucc]
  change Sum.inl (contractCoordinateEquiv A (.inl (.inr j)))=_
  rw [contractCoordinateEquiv_y]

/-- The new contract x slot is exactly the first new difference. -/
theorem slotInsertionEquiv_new_x {X : VineType} (A : Shape X) (hX : X ≠ .I) :
    slotInsertionEquiv A hX ((insertedShape A hX).xSlot (Fin.last A.m))=Sum.inr 0 := by
  rw [← contractCoordinateEquiv_x (insertedShape A hX) (Fin.last A.m)]
  rw [slotInsertionEquiv_on_tree]
  change Sum.map (contractCoordinateEquiv A) finSumFinEquiv
    (gatherAddedPair (Fin 1) (Fin A.m) (Fin A.m) (Fin (if X.IsBad then 0 else 3)) (Fin 1) (Fin 1)
      (.inl (.inl (.inr (finSumFinEquiv.symm (Fin.last A.m))))))=_
  rw [finSumFinEquiv_symm_last]
  rfl

/-- The new contract y slot is exactly the second new difference. -/
theorem slotInsertionEquiv_new_y {X : VineType} (A : Shape X) (hX : X ≠ .I) :
    slotInsertionEquiv A hX ((insertedShape A hX).ySlot (Fin.last A.m))=Sum.inr 1 := by
  rw [← contractCoordinateEquiv_y (insertedShape A hX) (Fin.last A.m)]
  rw [slotInsertionEquiv_on_tree]
  change Sum.map (contractCoordinateEquiv A) finSumFinEquiv
    (gatherAddedPair (Fin 1) (Fin A.m) (Fin A.m) (Fin (if X.IsBad then 0 else 3)) (Fin 1) (Fin 1)
      (.inl (.inr (finSumFinEquiv.symm (Fin.last A.m)))))=_
  rw [finSumFinEquiv_symm_last]
  rfl

/-- All three normal-core coordinates are retained verbatim. -/
theorem slotInsertionEquiv_core {X : VineType} (A : Shape X) (hX : X ≠ .I)
    (hn : X.IsBad=false) (j : Fin 3) :
    slotInsertionEquiv A hX ((insertedShape A hX).uSlot hn j)=Sum.inl (A.uSlot hn j) := by
  rw [← contractCoordinateEquiv_core (insertedShape A hX) hn j]
  rw [slotInsertionEquiv_on_tree]
  change Sum.inl (contractCoordinateEquiv A (.inr ⟨j.1,by simpa only [hn,Bool.false_eq_true,ite_false] using j.2⟩))=_
  rw [contractCoordinateEquiv_core]

end WaveTurbulence.Vine.Param
