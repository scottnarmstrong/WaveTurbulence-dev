/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulenceVineParam.Contract
public import WaveTurbulence.Foundations.Sumint.InputGrouping

/-! # Exact snapshot-9 shape and clock slots from the M9 chart family -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {I : ℕ}

def shapeFamily (X : Fin I → VineType) (A : ∀ i, Shape (X i)) : SumintShape where
  I := I
  m i := (A i).m
  nor i := !(X i).IsBad

theorem shapeFamily_n (X : Fin I → VineType) (A : ∀ i, Shape (X i)) (i : Fin I) :
    (shapeFamily X A).n i = (A i).n := by
  cases h : (X i).IsBad <;> simp only [shapeFamily,SumintShape.n,Shape.n,h,Bool.not_true,
    Bool.not_false,Bool.false_eq_true,ite_true,ite_false]

def familySlotEquiv (X : Fin I → VineType) (A : ∀ i, Shape (X i)) (i : Fin I) :
    Fin (A i).n ≃ Fin ((shapeFamily X A).n i) := finCongr (shapeFamily_n X A i).symm

theorem familySlotEquiv_x0 (X : Fin I → VineType) (A : ∀ i, Shape (X i)) (i : Fin I) :
    familySlotEquiv X A i (A i).x0 = ((shapeFamily X A).x0Slot i).2 := Fin.ext rfl

theorem familySlotEquiv_x (X : Fin I → VineType) (A : ∀ i, Shape (X i)) (i : Fin I) (j : Fin (A i).m) :
    familySlotEquiv X A i ((A i).xSlot j) = ((shapeFamily X A).xSlot i j).2 := Fin.ext rfl

theorem familySlotEquiv_y (X : Fin I → VineType) (A : ∀ i, Shape (X i)) (i : Fin I) (j : Fin (A i).m) :
    familySlotEquiv X A i ((A i).ySlot j) = ((shapeFamily X A).ySlot i j).2 := Fin.ext rfl

theorem shapeFamily_M (X : Fin I → VineType) (A : ∀ i, Shape (X i)) :
    (shapeFamily X A).M = ∑ i, (A i).n := by
  exact Finset.sum_congr rfl (fun i _ => shapeFamily_n X A i)

noncomputable def familyTimeEquiv (X : Fin I → VineType) (A : ∀ i, Shape (X i)) :
    (shapeFamily X A).TVar ≃ Σ i, Fin (A i).n :=
  (Sumint.timeVectorEquiv (shapeFamily X A)).trans (Equiv.sigmaCongrRight (familySlotEquiv X A)).symm

end WaveTurbulence.VineEstS2
