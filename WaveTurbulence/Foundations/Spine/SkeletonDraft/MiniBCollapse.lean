/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniPairedTreeEmbedding
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CollapsedPairs

/-! # Exact address and forest recovery for B-mini collapse -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree
namespace MiniBOccurrence

theorem collapse_path {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (hG : G.IsPlain) :
    (Comb.collapseDataOfDesc (h.isSubPairedTree hG).1).path = [m.c,m.lone] := by
  apply addrExt_path_injective b.1
  exact (collapseData_frame (h.isSubPairedTree hG).1).symm.trans h.lone_frame

/-- Extracting at the collapsed root gives the entire retained lone subtree. -/
theorem collapsed_subtree {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (hG : G.IsPlain) :
    Comb.subtree ((collapsePairedTreeGarden (h.isSubPairedTree hG)).tree b.1.1) b.1.2 =
      some (Comb.nodeSubtree (c.child m.lone)) := by
  change Comb.subtree (Comb.replaceNodeForest G.tree b.toNode _ b.1.1) b.1.2 = _
  simp only [Comb.replaceNodeForest,GBranch.toNode,Function.update_self]
  exact Comb.subtree_replaceAt (Comb.nodeSubtree_spec b.toNode) _

/-- B insertion into the collapsed forest restores the original literal ordered forest. -/
theorem recover_forest {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (hG : G.IsPlain) :
    ((rawOfGarden (collapsePairedTreeGarden (h.isSubPairedTree hG))).opB b.1 m).tree = G.tree := by
  have hs := subtreeAt_eq_of_subtree _ _ _ (h.collapsed_subtree hG)
  change Function.update (collapsePairedTreeGarden (h.isSubPairedTree hG)).tree b.1.1
    (((collapsePairedTreeGarden (h.isSubPairedTree hG)).tree b.1.1).setAt b.1.2
      (miniTreeContext m (((collapsePairedTreeGarden (h.isSubPairedTree hG)).tree b.1.1).subtreeAt b.1.2))) = _
  have hu : Comb.nodeSubtree b.toNode = miniTreeContext m (Comb.nodeSubtree (c.child m.lone)) := h.upper_tree
  rw [hs,← hu]
  funext j
  by_cases hj : j = b.1.1
  · subst j
    simp only [Function.update_self,setAt_eq_replaceAt]
    change Comb.replaceAt (Function.update G.tree b.1.1
      (Comb.replaceAt (G.tree b.1.1) b.1.2 (Comb.nodeSubtree (c.child m.lone))) b.1.1)
      b.1.2 (Comb.nodeSubtree b.toNode) = G.tree b.1.1
    rw [Function.update_self]
    exact (Comb.replaceAt_replaceAt (Comb.nodeSubtree_spec b.toNode) _ _).trans
      (Comb.replaceAt_self (Comb.nodeSubtree_spec b.toNode))
  · rw [Function.update_of_ne hj]
    change Comb.replaceNodeForest G.tree b.toNode _ j = G.tree j
    change Function.update G.tree b.1.1 _ j = G.tree j
    exact Function.update_of_ne hj _ _

end MiniBOccurrence
end WaveTurbulence.Reg.Skeleton
