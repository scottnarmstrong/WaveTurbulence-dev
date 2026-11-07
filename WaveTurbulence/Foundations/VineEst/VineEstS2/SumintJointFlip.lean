/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9ShapeSlots

/-! # The lattice involution normalizing the source and sumint gap signs -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2

/-- Only the joint variable changes sign; all rung and core variables stay
fixed. This compensates for the frozen r=e-f=-(g-h) convention. -/
def jointFlipSign (S : SumintShape) (v : S.VIdx) : ℤ := if v.2.val = 0 then -1 else 1

def jointFlip {E : Type*} [AddCommGroup E] (S : SumintShape) : (S.VIdx → E) ≃ (S.VIdx → E) where
  toFun x v := jointFlipSign S v • x v
  invFun x v := jointFlipSign S v • x v
  left_inv x := by
    funext v
    simp only [jointFlipSign]
    split <;> simp only [neg_one_zsmul,neg_neg,one_smul]
  right_inv x := by
    funext v
    simp only [jointFlipSign]
    split <;> simp only [neg_one_zsmul,neg_neg,one_smul]

theorem jointFlip_x0 {E : Type*} [AddCommGroup E] (S : SumintShape) (x : S.VIdx → E) (i : Fin S.I) :
    jointFlip S x (S.x0Slot i) = -x (S.x0Slot i) := by
  simp only [Equiv.coe_fn_mk,jointFlip,jointFlipSign,SumintShape.x0Slot,Equiv.coe_fn_mk,ite_true,neg_one_zsmul]

theorem jointFlip_x {E : Type*} [AddCommGroup E] (S : SumintShape) (x : S.VIdx → E)
    (i : Fin S.I) (j : Fin (S.m i)) : jointFlip S x (S.xSlot i j) = x (S.xSlot i j) := by
  simp only [Equiv.coe_fn_mk,jointFlip,jointFlipSign,SumintShape.xSlot]
  simp

theorem jointFlip_y {E : Type*} [AddCommGroup E] (S : SumintShape) (x : S.VIdx → E)
    (i : Fin S.I) (j : Fin (S.m i)) : jointFlip S x (S.ySlot i j) = x (S.ySlot i j) := by
  simp only [Equiv.coe_fn_mk,jointFlip,jointFlipSign,SumintShape.ySlot]
  simp

theorem jointFlip_u {E : Type*} [AddCommGroup E] (S : SumintShape) (x : S.VIdx → E)
    (i : Fin S.I) (h : S.nor i = true) (c : Fin 3) : jointFlip S x (S.uSlot i h c) = x (S.uSlot i h c) := by
  simp only [jointFlip,jointFlipSign,Equiv.coe_fn_mk,SumintShape.uSlot]
  simp

theorem jointFlip_unit (S : SumintShape) (v : S.VIdx) (a : ℤ) (ha : IsUnitCoeff a) :
    IsUnitCoeff (a * jointFlipSign S v) := by
  rcases ha with rfl | rfl | rfl <;> unfold jointFlipSign <;> split <;> norm_num [IsUnitCoeff]

end WaveTurbulence.VineEstS2
