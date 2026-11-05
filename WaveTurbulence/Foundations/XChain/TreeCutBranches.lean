/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeCutRetention
/-! Exact branching membership for a tree cut at a monotone layer boundary. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem cutTree_branching_subset (T : TTree) (stop : TTree.Path → Bool) :
    (cutTree T stop).branching ⊆ T.branching := by
  induction T generalizing stop with
  | leaf => exact fun _ h => h
  | node l m r hl hm hr =>
    by_cases hs : stop [] = true
    · simp only [cutTree, hs, ite_true, TTree.branching, empty_subset]
    · intro a ha
      simp only [cutTree, hs] at ha
      cases a with
      | nil => simp [TTree.branching]
      | cons i a =>
        apply (cons_mem_branching_node l m r i a).mpr
        have hc := (cons_mem_branching_node _ _ _ i a).mp ha
        fin_cases i
        · exact hl _ hc
        · exact hm _ hc
        · exact hr _ hc

theorem mem_cutTree_branching_of_no_stop (T : TTree) (stop : TTree.Path → Bool)
    (a : TTree.Path) (ha : a ∈ T.branching) (hs : stop a = false)
    (hn : ∀ r s, a = r ++ s → s ≠ [] → stop r = false) : a ∈ (cutTree T stop).branching := by
  induction a generalizing T stop with
  | nil =>
    cases T with
    | leaf => exact False.elim (notMem_empty _ ha)
    | node l m r => simp [cutTree, hs, TTree.branching]
  | cons i a ih =>
    cases T with
    | leaf => exact False.elim (notMem_empty _ ha)
    | node l m r =>
      have h0 := hn [] (i :: a) rfl (List.cons_ne_nil _ _)
      have hn' : ∀ u v, a = u ++ v → v ≠ [] → stop (i :: u) = false := by
        intro u v huv hv
        exact hn (i :: u) v (congrArg (List.cons i) huv) hv
      simp only [cutTree, h0, Bool.false_eq_true, ite_false]
      apply (cons_mem_branching_node _ _ _ i a).mpr
      have hc := (cons_mem_branching_node l m r i a).mp ha
      fin_cases i
      · exact ih l _ hc hs hn'
      · exact ih m _ hc hs hn'
      · exact ih r _ hc hs hn'

end WaveTurbulence.Induct
