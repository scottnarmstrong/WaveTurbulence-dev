/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseCoupleNodes
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniCoupleEmbedding

/-! # An A-mini collapse removes precisely its two branch labels -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem branch_below_corolla_iff {w : ℕ} (tree : Fin w → TTree) (b d : GBranch tree)
    (hb : Comb.nodeSubtree b.toNode = .node .leaf .leaf .leaf) : Below b.1 d.1 ↔ d = b := by
  constructor
  · intro h
    obtain ⟨p,hp⟩ := below_exists_frame b.1 d.1 h
    have hm : p ∈ (Comb.nodeSubtree b.toNode).branching := by
      apply (Comb.subtree_branching_iff (Comb.nodeSubtree_spec b.toNode) p).mpr
      change (addrExt b.1 p).2 ∈ (tree (addrExt b.1 p).1).branching
      rw [← hp]
      exact d.2
    rw [hb] at hm
    have he : p = [] := by simpa [TTree.branching,TTree.pre] using hm
    apply Subtype.ext
    rw [hp,he]
    exact Prod.ext rfl (List.append_nil _)
  · rintro rfl
    exact ⟨rfl,List.prefix_refl _⟩

/-- Exact range of the surviving actual branch embedding for a source A mini. -/
theorem MiniAOccurrence.branch_embedding_range {w : ℕ} {G : Garden w}
    {b c : GBranch G.tree} {k : MiniCplCode} (h : MiniAOccurrence G b c k) (hG : G.IsPlain)
    (d : GBranch G.tree) :
    d ∈ Set.range (collapseCoupleBranchEmbedding (h.isSubCouple hG)) ↔ d ≠ b ∧ d ≠ c := by
  constructor
  · rintro ⟨x,rfl⟩
    have hx := (collapsePairForest_branch_iff G.tree b.toNode c.toNode
      (Comb.subCouple_incomparable (h.isSubCouple hG)) x.1).mp x.2
    exact ⟨fun he => hx.2.1 ((branch_below_corolla_iff G.tree b _ h.left_tree).mpr he),
      fun he => hx.2.2 ((branch_below_corolla_iff G.tree c _ h.right_tree).mpr he)⟩
  · rintro ⟨hb,hc⟩
    have hx : d.1.2 ∈ ((collapseCoupleGarden (h.isSubCouple hG)).tree d.1.1).branching := by
      apply (collapsePairForest_branch_iff G.tree b.toNode c.toNode
        (Comb.subCouple_incomparable (h.isSubCouple hG)) d.1).mpr
      exact ⟨d.2,fun he => hb ((branch_below_corolla_iff G.tree b d h.left_tree).mp he),
        fun he => hc ((branch_below_corolla_iff G.tree c d h.right_tree).mp he)⟩
    exact ⟨⟨d.1,hx⟩,Subtype.ext rfl⟩

end WaveTurbulence.Reg.Skeleton
