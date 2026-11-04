/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeLeafRows

/-! # The actual C2 paired tree as a finite momentum-tree carrier -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

variable {G : Garden 1} {X : RegChain}

/-- Extend the actual node row by zero outside the finite source tree. -/
@[expose] def treeForestRow (hX : X.DecodesTree G) (i : Fin 1) (p : TTree.Path) :
    MomentumCoordinate (X.treeLinks (G.sig 0)).length → ℤ :=
  if hp : p ∈ (G.tree i).nodes then treeNodeRow hX ⟨(i, p), hp⟩ else 0

@[simp] theorem treeForestRow_node (hX : X.DecodesTree G) (a : GNode G.tree) :
    treeForestRow hX a.1.1 a.1.2 = treeNodeRow hX a := by
  rcases a with ⟨⟨i, p⟩, hp⟩
  simp only [treeForestRow, dite_eq_left hp]

/-- The exact finite integer carrier constructed from C2's source decoration equivalence. -/
@[expose] def treeCarrier (hX : X.DecodesTree G) :
    MomentumTreeData (X.treeLinks (G.sig 0)).length (Fintype.card (TPlus G)) 1 where
  tree i := treeShape (G.tree i)
  order_eq := by
    simp only [treeShape_order, Fin.sum_univ_one]
    rw [hX.1, Reg.code_plug_order, TTree.order, add_zero]
    simpa only [RegChain.treeLinks, Nat.mul_comm] using
      (Links.chain_linksAt_length X (G.sig 0) ((0 : Fin 1), [])).symm
  nodeRow := treeForestRow hX
  inputRow a := treeNodeRow hX ((treeInputEquiv G).symm a).1.toNode
  input_root_column := by intro a; rfl
  leafInput i p := if hp : p ∈ (G.tree i).leaves then treeLeafInput G ⟨(i, p), hp⟩ else none
  root_row := by
    intro i
    change treeForestRow hX (GNode.root G.tree i).1.1 (GNode.root G.tree i).1.2 = _
    rw [treeForestRow_node]
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi, treeNodeRow_root]
  parent_row := by
    intro i p hp
    rw [treeShape_branching] at hp
    let b : GBranch G.tree := ⟨(i, p), hp⟩
    change treeForestRow hX b.toNode.1.1 b.toNode.1.2 =
      treeForestRow hX (b.child 0).1.1 (b.child 0).1.2 -
      treeForestRow hX (b.child 1).1.1 (b.child 1).1.2 +
      treeForestRow hX (b.child 2).1.1 (b.child 2).1.2
    simp only [treeForestRow_node]
    exact treeNodeRow_parent hX b
  leaf_row := by
    intro i p hp
    rw [treeShape_leaves] at hp
    simp only [dite_eq_left hp]
    change treeForestRow hX (GLeaf.toNode ⟨(i, p), hp⟩).1.1
      (GLeaf.toNode ⟨(i, p), hp⟩).1.2 = _
    rw [treeForestRow_node]
    have he := treeNodeRow_leaf hX ⟨(i, p), hp⟩
    cases ho : treeLeafInput G ⟨(i, p), hp⟩ <;> simp only [ho] at he ⊢ <;> exact he
  chosenTree j := (treeChosenBranch hX j).1.1
  chosenPath j := (treeChosenBranch hX j).1.2
  chosen_mem_nodes j := by rw [treeShape_nodes]; exact (treeChosenBranch hX j).toNode.2
  child0_mem_nodes j := by rw [treeShape_nodes]; exact ((treeChosenBranch hX j).child 0).2
  child2_mem_nodes j := by rw [treeShape_nodes]; exact ((treeChosenBranch hX j).child 2).2
  link_x_row := by
    intro j
    change treeForestRow hX ((treeChosenBranch hX j).child 0).1.1 ((treeChosenBranch hX j).child 0).1.2 -
      treeForestRow hX (treeChosenBranch hX j).toNode.1.1 (treeChosenBranch hX j).toNode.1.2 = _
    simp only [treeForestRow_node]
    exact treeNodeRow_link_x hX j
  link_y_row := by
    intro j
    change treeForestRow hX (treeChosenBranch hX j).toNode.1.1 (treeChosenBranch hX j).toNode.1.2 -
      treeForestRow hX ((treeChosenBranch hX j).child 2).1.1 ((treeChosenBranch hX j).child 2).1.2 = _
    simp only [treeForestRow_node]
    exact treeNodeRow_link_y hX j

end WaveTurbulence.IncohInst
