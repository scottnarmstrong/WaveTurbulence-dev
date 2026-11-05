/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! # The two-joint budget on distinct rung atoms (TARGET subsetvc) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {A : Type*} [DecidableEq A]

/-- The membership indicator for the actual joint set. -/
@[expose] def jointIndicator (J : Finset A) (x : A) : ℕ := if x ∈ J then 1 else 0

/-- Distinct atoms can use each joint at most once. -/
theorem sum_jointIndicator_le {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset A) (f : I → A) (hf : Function.Injective f) :
    ∑ i : I,jointIndicator J (f i) ≤ J.card := by
  let T := univ.filter fun i => f i ∈ J
  have hsub : T.image f ⊆ J := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp hi).2
  calc
    _ = T.card := by simp only [jointIndicator,T,sum_boole,Nat.cast_id]
    _ = (T.image f).card := (card_image_of_injective T hf).symm
    _ ≤ J.card := card_le_card hsub

/-- The six distinct atoms of a three-rung window use at most two joints. -/
theorem three_rung_joint_budget (J : Finset A) (hJ : J.card≤2)
    (a b c d e f : A) (hinj : Function.Injective ![a,b,c,d,e,f]) :
    jointIndicator J a+jointIndicator J b+jointIndicator J c+
      jointIndicator J d+jointIndicator J e+jointIndicator J f≤2 := by
  have hh := (sum_jointIndicator_le J ![a,b,c,d,e,f] hinj).trans hJ
  simpa only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero,Nat.add_assoc] using hh

end WaveTurbulence.Vine
