/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Structure

/-! # Every incoming node slot is a root slot or an ordered branching child slot -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Incoming tree-edge slots, without a choice of enumeration. -/
abbrev NodeSlot {w : ℕ} (tree : Fin w → TTree) := Fin w ⊕ (GBranch tree × Fin 3)

/-- Locate an incoming node slot by its actual parent and final child index. -/
def nodeToSlot {w : ℕ} {tree : Fin w → TTree} (a : GNode tree) : NodeSlot tree :=
  if h : a.1.2 = [] then .inl a.1.1
  else .inr (a.parent h,a.1.2.getLast h)

/-- A root slot denotes the root, and a child slot denotes that actual child node. -/
def slotToNode {w : ℕ} (tree : Fin w → TTree) : NodeSlot tree → GNode tree
  | .inl j => GNode.root tree j
  | .inr (b,i) => b.child i

theorem child_nonroot {w : ℕ} {tree : Fin w → TTree} (b : GBranch tree) (i : Fin 3) :
    (b.child i).1.2 ≠ [] := by simp [GBranch.child]

theorem parent_child {w : ℕ} {tree : Fin w → TTree} (b : GBranch tree) (i : Fin 3) :
    (b.child i).parent (child_nonroot b i) = b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simp [GNode.parent,GBranch.child]

theorem child_parent {w : ℕ} {tree : Fin w → TTree} (a : GNode tree) (ha : a.1.2 ≠ []) :
    (a.parent ha).child (a.1.2.getLast ha) = a := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact List.dropLast_append_getLast ha

theorem nodeToSlot_child {w : ℕ} {tree : Fin w → TTree} (b : GBranch tree) (i : Fin 3) :
    nodeToSlot (b.child i) = .inr (b,i) := by
  rw [nodeToSlot,dite_eq_right (child_nonroot b i),parent_child]
  apply congrArg Sum.inr
  apply Prod.ext
  · rfl
  · exact List.getLast_append_singleton b.1.2

/-- Incoming slots give an exact bijection with the actual node set. -/
def nodeSlotEquiv {w : ℕ} (tree : Fin w → TTree) : GNode tree ≃ NodeSlot tree where
  toFun := nodeToSlot
  invFun := slotToNode tree
  left_inv a := by
    by_cases ha : a.1.2 = []
    · rw [nodeToSlot,dite_eq_left ha]
      exact Subtype.ext (Prod.ext rfl ha.symm)
    · rw [nodeToSlot,dite_eq_right ha]
      exact child_parent a ha
  right_inv x := by
    cases x with
    | inl j => simp [slotToNode,nodeToSlot,GNode.root]
    | inr x => exact nodeToSlot_child x.1 x.2

end WaveTurbulence.Reg.Skeleton
