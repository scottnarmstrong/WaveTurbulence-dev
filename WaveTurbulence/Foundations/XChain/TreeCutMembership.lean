/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeCut
/-! Nodes retained by a cut and the exact stopping condition at each cut leaf. -/
public section
namespace WaveTurbulence.Induct
open Finset TTree

theorem cons_mem_nodes_node (l m r : TTree) (i : Fin 3) (a : TTree.Path) :
    i :: a ∈ (TTree.node l m r).nodes ↔ a ∈ (![l, m, r] i).nodes := by
  fin_cases i <;> simp [TTree.nodes, TTree.cons_mem_pre]

theorem cons_mem_leaves_node (l m r : TTree) (i : Fin 3) (a : TTree.Path) :
    i :: a ∈ (TTree.node l m r).leaves ↔ a ∈ (![l, m, r] i).leaves := by
  fin_cases i <;> simp [TTree.leaves, TTree.cons_mem_pre]

theorem cons_mem_branching_node (l m r : TTree) (i : Fin 3) (a : TTree.Path) :
    i :: a ∈ (TTree.node l m r).branching ↔ a ∈ (![l, m, r] i).branching := by
  fin_cases i <;> simp [TTree.branching, TTree.cons_mem_pre]

theorem cutTree_nodes_subset (T : TTree) (stop : TTree.Path → Bool) :
    (cutTree T stop).nodes ⊆ T.nodes := by
  induction T generalizing stop with
  | leaf => exact fun _ h => h
  | node l m r hl hm hr =>
    by_cases hs : stop [] = true
    · intro a ha
      have he : a = [] := by simpa only [cutTree, hs, ite_true, TTree.nodes, mem_singleton] using ha
      exact he ▸ TTree.nil_mem_nodes _
    · intro a ha
      simp only [cutTree, hs] at ha
      rcases a with _ | ⟨i, a⟩
      · exact TTree.nil_mem_nodes _
      · fin_cases i
        · exact (cons_mem_nodes_node l m r 0 a).mpr
            (hl _ ((cons_mem_nodes_node _ _ _ 0 a).mp ha))
        · exact (cons_mem_nodes_node l m r 1 a).mpr
            (hm _ ((cons_mem_nodes_node _ _ _ 1 a).mp ha))
        · exact (cons_mem_nodes_node l m r 2 a).mpr
            (hr _ ((cons_mem_nodes_node _ _ _ 2 a).mp ha))

theorem stop_false_of_mem_cutTree_branching (T : TTree) (stop : TTree.Path → Bool)
    {a : TTree.Path} (ha : a ∈ (cutTree T stop).branching) : stop a = false := by
  induction T generalizing stop a with
  | leaf => exact False.elim (Finset.notMem_empty _ ha)
  | node l m r hl hm hr =>
    by_cases hs : stop [] = true
    · simp only [cutTree, hs, ite_true, TTree.branching, notMem_empty] at ha
    · simp only [cutTree, hs] at ha
      rcases a with _ | ⟨i, a⟩
      · exact Bool.eq_false_iff.mpr hs
      · fin_cases i
        · exact hl (fun a => stop (0 :: a)) ((cons_mem_branching_node _ _ _ 0 a).mp ha)
        · exact hm (fun a => stop (1 :: a)) ((cons_mem_branching_node _ _ _ 1 a).mp ha)
        · exact hr (fun a => stop (2 :: a)) ((cons_mem_branching_node _ _ _ 2 a).mp ha)

theorem cutTree_leaf_is_original_or_stop (T : TTree) (stop : TTree.Path → Bool)
    {a : TTree.Path} (ha : a ∈ (cutTree T stop).leaves) : a ∈ T.leaves ∨ stop a = true := by
  induction T generalizing stop a with
  | leaf => exact Or.inl ha
  | node l m r hl hm hr =>
    by_cases hs : stop [] = true
    · have he : a = [] := by simpa only [cutTree, hs, ite_true, TTree.leaves, mem_singleton] using ha
      exact Or.inr (he ▸ hs)
    · simp only [cutTree, hs] at ha
      rcases a with _ | ⟨i, a⟩
      · simp [TTree.leaves, TTree.pre] at ha
      · fin_cases i
        · exact (hl (fun a => stop (0 :: a)) ((cons_mem_leaves_node _ _ _ 0 a).mp ha)).imp_left
            ((cons_mem_leaves_node l m r 0 a).mpr)
        · exact (hm (fun a => stop (1 :: a)) ((cons_mem_leaves_node _ _ _ 1 a).mp ha)).imp_left
            ((cons_mem_leaves_node l m r 1 a).mpr)
        · exact (hr (fun a => stop (2 :: a)) ((cons_mem_leaves_node _ _ _ 2 a).mp ha)).imp_left
            ((cons_mem_leaves_node l m r 2 a).mpr)

end WaveTurbulence.Induct
