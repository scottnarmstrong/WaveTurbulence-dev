/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeCutMembership
/-! Exact node, leaf and branching membership below any original tree node. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset TTree

theorem subtreeAt_nodes_iff (T : TTree) (a : TTree.Path) (ha : a ∈ T.nodes) (b : TTree.Path) :
    b ∈ (subtreeAt T a).nodes ↔ a ++ b ∈ T.nodes := by
  induction a generalizing T with
  | nil => rfl
  | cons i a ih =>
    cases T with
    | leaf => simp only [TTree.nodes, mem_singleton, List.cons_ne_nil] at ha
    | node l m r =>
      change b ∈ (subtreeAt (![l, m, r] i) a).nodes ↔ i :: (a ++ b) ∈ (TTree.node l m r).nodes
      rw [cons_mem_nodes_node]
      exact ih _ ((cons_mem_nodes_node l m r i a).mp ha)

theorem subtreeAt_leaves_iff (T : TTree) (a : TTree.Path) (ha : a ∈ T.nodes) (b : TTree.Path) :
    b ∈ (subtreeAt T a).leaves ↔ a ++ b ∈ T.leaves := by
  induction a generalizing T with
  | nil => rfl
  | cons i a ih =>
    cases T with
    | leaf => simp only [TTree.nodes, mem_singleton, List.cons_ne_nil] at ha
    | node l m r =>
      change b ∈ (subtreeAt (![l, m, r] i) a).leaves ↔ i :: (a ++ b) ∈ (TTree.node l m r).leaves
      rw [cons_mem_leaves_node]
      exact ih _ ((cons_mem_nodes_node l m r i a).mp ha)

theorem subtreeAt_branching_iff (T : TTree) (a : TTree.Path) (ha : a ∈ T.nodes) (b : TTree.Path) :
    b ∈ (subtreeAt T a).branching ↔ a ++ b ∈ T.branching := by
  induction a generalizing T with
  | nil => rfl
  | cons i a ih =>
    cases T with
    | leaf => simp only [TTree.nodes, mem_singleton, List.cons_ne_nil] at ha
    | node l m r =>
      change b ∈ (subtreeAt (![l, m, r] i) a).branching ↔ i :: (a ++ b) ∈ (TTree.node l m r).branching
      rw [cons_mem_branching_node]
      exact ih _ ((cons_mem_nodes_node l m r i a).mp ha)

theorem subtreeAt_eq_leaf_of_mem_leaves (T : TTree) {a : TTree.Path} (ha : a ∈ T.leaves) :
    subtreeAt T a = TTree.leaf := by
  have he := subtreeAt_graftTree_leaf T (fun _ => TTree.leaf) ha
  exact (congrArg (fun S => subtreeAt S a) (graftTree_leaf T)).symm.trans he

end WaveTurbulence.Induct
