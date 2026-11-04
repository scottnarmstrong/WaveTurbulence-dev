/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleRows
public import WaveTurbulence.Foundations.Incoh.RootInputCoordinates

/-! # The actual C2 couple as a finite momentum-tree carrier -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links

variable {G : Garden 2} {Q : RegCpl}

/-- Enumerate the actual positive leaves, without changing their source multiplicities. -/
@[expose] def coupleInputEquiv (G : Garden 2) : PlusLeaf G ≃ Fin (Fintype.card (PlusLeaf G)) :=
  Fintype.equivFin _

/-- Every source leaf uses its positive representative in the source pairing. -/
@[expose] def couplePositiveLeaf (hG : IsCouple G) (a : GLeaf G.tree) : PlusLeaf G :=
  if ha : a ∈ plusLeaves G then ⟨a, (mem_plusLeaves a).1 ha⟩ else
    ⟨G.pair a, (mem_plusLeaves (G.pair a)).1 ((pair_mem_plus_iff hG.1 a).2 ha)⟩

theorem coupleNodeRow_positive (hQ : Q.Decodes G) (hG : IsCouple G) (a : GLeaf G.tree) :
    coupleNodeRow hQ (couplePositiveLeaf hG a).1.toNode = coupleNodeRow hQ a.toNode := by
  unfold couplePositiveLeaf
  split_ifs
  · rfl
  · exact (coupleNodeRow_pair hQ a).symm

/-- Extend the actual node row by zero outside the finite source tree. -/
@[expose] def coupleForestRow (hQ : Q.Decodes G) (i : Fin 2) (p : TTree.Path) :
    MomentumCoordinate Q.links.length → ℤ :=
  if hp : p ∈ (G.tree i).nodes then coupleNodeRow hQ ⟨(i, p), hp⟩ else 0

@[simp] theorem coupleForestRow_node (hQ : Q.Decodes G) (a : GNode G.tree) :
    coupleForestRow hQ a.1.1 a.1.2 = coupleNodeRow hQ a := by
  rcases a with ⟨⟨i, p⟩, hp⟩
  simp only [coupleForestRow, dite_eq_left hp]

/-- The exact finite integer carrier constructed from C2's source decoration equivalence. -/
@[expose] def coupleCarrier (hQ : Q.Decodes G) :
    MomentumTreeData Q.links.length (Fintype.card (PlusLeaf G)) 2 where
  tree i := treeShape (G.tree i)
  order_eq := by
    simp only [treeShape_order, Fin.sum_univ_two]
    rw [hQ.2.1, hQ.2.2.1, Reg.code_trees_order]
    simpa only [RegCpl.links, Nat.mul_comm] using
      (Links.couple_linksAt_length Q ((0 : Fin 2), []) ((1 : Fin 2), [])).symm
  nodeRow := coupleForestRow hQ
  inputRow a := coupleNodeRow hQ ((coupleInputEquiv G).symm a).1.toNode
  input_root_column := by intro a; rfl
  leafInput i p := if hp : p ∈ (G.tree i).leaves then
    some (coupleInputEquiv G (couplePositiveLeaf hQ.1 ⟨(i, p), hp⟩)) else none
  root_row := by
    intro i
    change coupleForestRow hQ (GNode.root G.tree i).1.1 (GNode.root G.tree i).1.2 = _
    rw [coupleForestRow_node, coupleNodeRow_root]
  parent_row := by
    intro i p hp
    rw [treeShape_branching] at hp
    let b : GBranch G.tree := ⟨(i, p), hp⟩
    change coupleForestRow hQ b.toNode.1.1 b.toNode.1.2 =
      coupleForestRow hQ (b.child 0).1.1 (b.child 0).1.2 -
      coupleForestRow hQ (b.child 1).1.1 (b.child 1).1.2 +
      coupleForestRow hQ (b.child 2).1.1 (b.child 2).1.2
    simp only [coupleForestRow_node]
    exact coupleNodeRow_parent hQ b
  leaf_row := by
    intro i p hp
    rw [treeShape_leaves] at hp
    simp only [dite_eq_left hp, Equiv.symm_apply_apply]
    change coupleForestRow hQ (GLeaf.toNode ⟨(i, p), hp⟩).1.1
      (GLeaf.toNode ⟨(i, p), hp⟩).1.2 = _
    rw [coupleForestRow_node]
    exact (coupleNodeRow_positive hQ hQ.1 ⟨(i, p), hp⟩).symm
  chosenTree j := (chosenBranch hQ j).1.1
  chosenPath j := (chosenBranch hQ j).1.2
  chosen_mem_nodes j := by rw [treeShape_nodes]; exact (chosenBranch hQ j).toNode.2
  child0_mem_nodes j := by rw [treeShape_nodes]; exact ((chosenBranch hQ j).child 0).2
  child2_mem_nodes j := by rw [treeShape_nodes]; exact ((chosenBranch hQ j).child 2).2
  link_x_row := by
    intro j
    change coupleForestRow hQ ((chosenBranch hQ j).child 0).1.1 ((chosenBranch hQ j).child 0).1.2 -
      coupleForestRow hQ (chosenBranch hQ j).toNode.1.1 (chosenBranch hQ j).toNode.1.2 = _
    simp only [coupleForestRow_node]
    exact coupleNodeRow_link_x hQ hQ.1 j
  link_y_row := by
    intro j
    change coupleForestRow hQ (chosenBranch hQ j).toNode.1.1 (chosenBranch hQ j).toNode.1.2 -
      coupleForestRow hQ ((chosenBranch hQ j).child 2).1.1 ((chosenBranch hQ j).child 2).1.2 = _
    simp only [coupleForestRow_node]
    exact coupleNodeRow_link_y hQ hQ.1 j

end WaveTurbulence.IncohInst
