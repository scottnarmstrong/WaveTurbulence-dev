/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CollapseForestRecovery
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniCoupleEmbedding

/-! # Literal ordered forest recovery for A-mini collapse -/

public section
namespace WaveTurbulence.Reg.Skeleton
namespace MiniAOccurrence

/-- Reinserting the two corollas restores the complete original forest. -/
theorem recover_forest {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {k : MiniCplCode}
    (h : MiniAOccurrence G b c k) (hG : G.IsPlain) :
    ((rawOfGarden (collapseCoupleGarden (h.isSubCouple hG))).opA b.1 c.1 k).tree = G.tree := by
  have ht := collapsePairForest_recover G.tree b.toNode c.toNode
    (Comb.subCouple_incomparable (h.isSubCouple hG))
  rw [h.left_tree,h.right_tree] at ht
  simp only [Raw.opA,rawOfGarden,setAt_eq_replaceAt]
  exact ht

end MiniAOccurrence
end WaveTurbulence.Reg.Skeleton
