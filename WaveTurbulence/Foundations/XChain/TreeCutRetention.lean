/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeCutMembership
/-! Original nodes and leaves are retained when no strict ancestor is a stopping node. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem mem_cutTree_nodes_of_no_strict_stop (T : TTree) (stop : TTree.Path → Bool)
    (a : TTree.Path) (ha : a ∈ T.nodes)
    (hn : ∀ r s, a = r ++ s → s ≠ [] → stop r = false) : a ∈ (cutTree T stop).nodes := by
  induction a generalizing T stop with
  | nil => exact TTree.nil_mem_nodes _
  | cons i a ih =>
    cases T with
    | leaf => simp only [TTree.nodes, mem_singleton, List.cons_ne_nil] at ha
    | node l m r =>
      have hs := hn [] (i :: a) rfl (List.cons_ne_nil _ _)
      have hn' : ∀ u v, a = u ++ v → v ≠ [] → stop (i :: u) = false := by
        intro u v huv hv
        exact hn (i :: u) v (congrArg (List.cons i) huv) hv
      simp only [cutTree, hs, Bool.false_eq_true, ite_false]
      apply (cons_mem_nodes_node _ _ _ i a).mpr
      have ha' := (cons_mem_nodes_node l m r i a).mp ha
      fin_cases i
      · exact ih l _ ha' hn'
      · exact ih m _ ha' hn'
      · exact ih r _ ha' hn'

theorem mem_cutTree_leaves_of_no_strict_stop (T : TTree) (stop : TTree.Path → Bool)
    (a : TTree.Path) (ha : a ∈ T.leaves)
    (hn : ∀ r s, a = r ++ s → s ≠ [] → stop r = false) : a ∈ (cutTree T stop).leaves := by
  induction a generalizing T stop with
  | nil =>
    cases T with
    | leaf => exact ha
    | node l m r => simp [TTree.leaves, TTree.pre] at ha
  | cons i a ih =>
    cases T with
    | leaf => simp only [TTree.leaves, mem_singleton, List.cons_ne_nil] at ha
    | node l m r =>
      have hs := hn [] (i :: a) rfl (List.cons_ne_nil _ _)
      have hn' : ∀ u v, a = u ++ v → v ≠ [] → stop (i :: u) = false := by
        intro u v huv hv
        exact hn (i :: u) v (congrArg (List.cons i) huv) hv
      simp only [cutTree, hs, Bool.false_eq_true, ite_false]
      apply (cons_mem_leaves_node _ _ _ i a).mpr
      have ha' := (cons_mem_leaves_node l m r i a).mp ha
      fin_cases i
      · exact ih l _ ha' hn'
      · exact ih m _ ha' hn'
      · exact ih r _ ha' hn'

end WaveTurbulence.Induct
