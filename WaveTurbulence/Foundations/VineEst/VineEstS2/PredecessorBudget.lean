/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.SubtreeProduct

/-! # Exponential predecessor coefficient budgets from DH21 Lemma 6.6 -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree

/-- Three times the second-largest leaf count pays for the two side subtrees
and the one boundary label in a signed predecessor identity. -/
def predecessorCostProduct : TTree → ℕ
  | .leaf => 1
  | .node l m r => (3*medianThree (leafCount l) (leafCount m) (leafCount r))*
      (predecessorCostProduct l*predecessorCostProduct m*predecessorCostProduct r)

theorem predecessorCostProduct_eq (T : TTree) :
    predecessorCostProduct T = 3^T.order*secondLeafProduct T := by
  induction T with
  | leaf => rfl
  | node l m r hl hm hr =>
    rw [predecessorCostProduct,hl,hm,hr,secondLeafProduct,TTree.order]
    simp only [pow_add,pow_one]
    ring

/-- A source-independent numerical budget with universal constant nine. -/
theorem predecessorCostProduct_le (T : TTree) : predecessorCostProduct T ≤ 9^T.order := by
  have h : secondLeafProduct T ≤ 3^T.order := by
    calc
      _ ≤ leafCount T*secondLeafProduct T := by
        simpa only [one_mul] using Nat.mul_le_mul_right (secondLeafProduct T)
          (show 1 ≤ leafCount T by unfold leafCount; omega)
      _ ≤ _ := leafCount_mul_secondLeafProduct T
  rw [predecessorCostProduct_eq]
  calc
    3^T.order*secondLeafProduct T ≤ 3^T.order*3^T.order := Nat.mul_le_mul_left _ h
    _ = 9^T.order := by rw [← mul_pow]; rfl

end WaveTurbulence.VineEstS2
