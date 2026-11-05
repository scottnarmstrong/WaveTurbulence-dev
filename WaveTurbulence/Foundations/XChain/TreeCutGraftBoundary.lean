/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeCutMembership
/-! A graft cut at its top/lower boundary recovers the original ordered top tree. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem cutTree_of_stop_root (T : TTree) (stop : TTree.Path → Bool) (hs : stop [] = true) :
    cutTree T stop = TTree.leaf := by
  cases T with
  | leaf => rfl
  | node l m r => simp only [cutTree, hs, ite_true]

theorem cutTree_graft_boundary (T : TTree) (f : TTree.Path → TTree) (stop : TTree.Path → Bool)
    (hb : ∀ a ∈ T.branching, stop a = false)
    (hl : ∀ a ∈ T.leaves, f a = TTree.leaf ∨ stop a = true) :
    cutTree (graftTree T f) stop = T := by
  induction T generalizing f stop with
  | leaf =>
    rcases hl [] (by simp only [TTree.leaves, mem_singleton]) with h | h
    · change cutTree (f []) stop = TTree.leaf
      rw [h]
      rfl
    · exact cutTree_of_stop_root (f []) stop h
  | node l m r ihl ihm ihr =>
    have hs := hb [] (by simp only [TTree.branching, mem_insert, true_or])
    have hbl : ∀ a ∈ l.branching, stop (0 :: a) = false := fun a ha =>
      hb (0 :: a) ((cons_mem_branching_node l m r 0 a).mpr ha)
    have hbm : ∀ a ∈ m.branching, stop (1 :: a) = false := fun a ha =>
      hb (1 :: a) ((cons_mem_branching_node l m r 1 a).mpr ha)
    have hbr : ∀ a ∈ r.branching, stop (2 :: a) = false := fun a ha =>
      hb (2 :: a) ((cons_mem_branching_node l m r 2 a).mpr ha)
    have hll : ∀ a ∈ l.leaves, f (0 :: a) = TTree.leaf ∨ stop (0 :: a) = true := fun a ha =>
      hl (0 :: a) ((cons_mem_leaves_node l m r 0 a).mpr ha)
    have hlm : ∀ a ∈ m.leaves, f (1 :: a) = TTree.leaf ∨ stop (1 :: a) = true := fun a ha =>
      hl (1 :: a) ((cons_mem_leaves_node l m r 1 a).mpr ha)
    have hlr : ∀ a ∈ r.leaves, f (2 :: a) = TTree.leaf ∨ stop (2 :: a) = true := fun a ha =>
      hl (2 :: a) ((cons_mem_leaves_node l m r 2 a).mpr ha)
    simp only [graftTree, cutTree, hs, Bool.false_eq_true, ite_false]
    exact congrArg₂ (fun x yz => TTree.node x yz.1 yz.2)
      (ihl (fun a => f (0 :: a)) (fun a => stop (0 :: a)) hbl hll)
      (congrArg₂ Prod.mk (ihm (fun a => f (1 :: a)) (fun a => stop (1 :: a)) hbm hlm)
        (ihr (fun a => f (2 :: a)) (fun a => stop (2 :: a)) hbr hlr))

end WaveTurbulence.Induct
