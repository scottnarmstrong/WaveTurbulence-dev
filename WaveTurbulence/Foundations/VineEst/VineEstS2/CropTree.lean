/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Trees

/-! # Cutting a genuine ternary tree at prescribed exterior subtrees -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree

/-- Retain a branching node only while its ancestor chain is retained. Cutting
an exterior subtree leaves its actual root as a boundary leaf. -/
def cropTree : TTree → (Path → Bool) → TTree
  | .leaf,_ => .leaf
  | .node l m r,keep => if keep [] then
      .node (cropTree l (fun p => keep (0::p))) (cropTree m (fun p => keep (1::p)))
        (cropTree r (fun p => keep (2::p))) else .leaf

theorem cropTree_nodes_subset (T : TTree) (keep : Path → Bool) :
    (cropTree T keep).nodes ⊆ T.nodes := by
  induction T generalizing keep with
  | leaf => exact Finset.Subset.refl _
  | node l m r hl hm hr =>
    unfold cropTree
    split
    · simp only [nodes]
      apply Finset.insert_subset_insert
      exact Finset.union_subset_union (Finset.union_subset_union
        (Finset.image_mono _ (hl _)) (Finset.image_mono _ (hm _))) (Finset.image_mono _ (hr _))
    · exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)

theorem cropTree_branching_subset (T : TTree) (keep : Path → Bool) :
    (cropTree T keep).branching ⊆ T.branching := by
  induction T generalizing keep with
  | leaf => exact Finset.Subset.refl _
  | node l m r hl hm hr =>
    unfold cropTree
    split
    · simp only [branching]
      apply Finset.insert_subset_insert
      exact Finset.union_subset_union (Finset.union_subset_union
        (Finset.image_mono _ (hl _)) (Finset.image_mono _ (hm _))) (Finset.image_mono _ (hr _))
    · exact Finset.empty_subset _

end WaveTurbulence.VineEstS2
