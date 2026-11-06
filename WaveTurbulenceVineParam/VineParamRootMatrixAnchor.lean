/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamRootMatrixFiber
import Mathlib.Tactic

/-! # The anchor-translated exact source chart and physical coordinate origins -/

public section
namespace WaveTurbulence.Vine.Param.RootIntegerMatrix
open Finset
variable {q : ℕ} (C : RootIntegerMatrix q) {E : Type*} [AddCommGroup E]

/-- Balanced source degrees make uniform anchor translation an exact
bijection on the full root-flow fiber. -/
@[expose] def anchorShift (g r : E) :
    DirectedRootFiber C.ends C.a C.b r ≃ DirectedRootFiber C.ends C.a C.b r where
  toFun := fun k => ⟨fun e => k.1 e+g,by
    intro v
    rw [directedFlow_translate,C.balanced,zero_zsmul,add_zero]
    exact k.2 v⟩
  invFun := fun k => ⟨fun e => k.1 e-g,by
    intro v
    rw [C.flow_sub_anchor]
    exact k.2 v⟩
  left_inv := by intro k; apply Subtype.ext; funext e; exact add_sub_cancel_right _ _
  right_inv := by intro k; apply Subtype.ext; funext e; exact sub_add_cancel _ _

/-- The normalized source chart subtracts g uniformly before its fixed
integer encoder, retaining all labels and all conservation equations. -/
@[expose] def affineChart (g r : E) : DirectedRootFiber C.ends C.a C.b r ≃ (Fin q → E) :=
  (C.anchorShift g r).symm.trans (C.rootChart r)

/-- Every actual decoded label has coefficient1 on the anchor. -/
theorem affineChart_decode (g r : E) (x : Fin q → E) (e : Fin (2*q)) :
    ((C.affineChart g r).symm x).1 e=g+intEval C.inverse (packCoordinates C.gap_lt x r) e := by
  change intEval C.inverse (packCoordinates C.gap_lt x r) e+g=_
  exact add_comm _ _

/-- The forward map is the literal normalized integer source encoder. -/
theorem affineChart_encode (g r : E) (k : DirectedRootFiber C.ends C.a C.b r) (i : Fin q) :
    C.affineChart g r k i=intEval C.forward (fun e => k.1 e-g) (C.freeIndex i) := rfl

/-- A checked physical reference row gives exactly g minus an actual bond. -/
theorem affineChart_reference_of_row (ref : Fin q) (out : Fin (2*q))
    (hrow : ∀ e,C.forward (C.freeIndex ref) e= -(if e=out then 1 else 0))
    (g r : E) (k : DirectedRootFiber C.ends C.a C.b r) :
    C.affineChart g r k ref=g-k.1 out := by
  rw [C.affineChart_encode]
  simp [intEval,hrow,neg_smul]

/-- A checked difference row is a fixed actual-bond difference after the
anchor translation. The same proof works on the integer lattice. -/
theorem affineChart_difference_of_row (i : Fin q) (p s : Fin (2*q))
    (hrow : ∀ e,C.forward (C.freeIndex i) e=(if e=p then 1 else 0)-(if e=s then 1 else 0))
    (g r : E) (k : DirectedRootFiber C.ends C.a C.b r) :
    C.affineChart g r k i=k.1 p-k.1 s := by
  rw [C.affineChart_encode]
  simp [intEval,hrow,sub_smul,sum_sub_distrib]

end WaveTurbulence.Vine.Param.RootIntegerMatrix
