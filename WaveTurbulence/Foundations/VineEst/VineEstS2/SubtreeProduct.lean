/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.MedianLeafBound

/-! # The exponential subtree product bound, DH21 Lemma 6.6 (auxineq) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree

/-- The actual number of leaves of a ternary tree. -/
def leafCount (T : TTree) : ℕ := 2*T.order+1

/-- Product of the second-largest child subtree's leaf count over every
branching node. The recursive body is the literal finite branching product. -/
def secondLeafProduct : TTree → ℕ
  | .leaf => 1
  | .node l m r => medianThree (leafCount l) (leafCount m) (leafCount r) *
      (secondLeafProduct l*secondLeafProduct m*secondLeafProduct r)

theorem leafCount_node (l m r : TTree) :
    leafCount (.node l m r) = leafCount l+leafCount m+leafCount r := by
  simp only [leafCount,TTree.order]
  omega

/-- DH21 Lemma 6.6, division-free exact constant 3^n/(2n+1). -/
theorem leafCount_mul_secondLeafProduct (T : TTree) :
    leafCount T * secondLeafProduct T ≤ 3^T.order := by
  induction T with
  | leaf => decide
  | node l m r hl hm hr =>
    rw [secondLeafProduct,leafCount_node]
    have hs := medianThree_leaf_bound (leafCount l) (leafCount m) (leafCount r)
      (by unfold leafCount; omega) (by unfold leafCount; omega) (by unfold leafCount; omega)
    calc
      _ ≤ (3*(leafCount l*leafCount m*leafCount r))*
          (secondLeafProduct l*secondLeafProduct m*secondLeafProduct r) := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right
          (secondLeafProduct l*secondLeafProduct m*secondLeafProduct r) hs
      _ = 3*((leafCount l*secondLeafProduct l)*(leafCount m*secondLeafProduct m)*
          (leafCount r*secondLeafProduct r)) := by ring
      _ ≤ 3*((3^l.order)*(3^m.order)*(3^r.order)) :=
        Nat.mul_le_mul_left 3 (Nat.mul_le_mul (Nat.mul_le_mul hl hm) hr)
      _ = 3^(TTree.node l m r).order := by rw [TTree.order]; simp only [pow_add,pow_one]; ring

end WaveTurbulence.VineEstS2
