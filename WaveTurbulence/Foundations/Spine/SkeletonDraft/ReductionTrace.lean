/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GardenGraphHistories

/-! # Explicit source surgery traces with exact inherited branch embeddings

The trace retains actual mini data in Type, allowing its branch embedding to be
computed without eliminating the propositional reduction relation into data.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Finite actual mini-collapse data, including the identity and concatenation. -/
inductive ReductionTrace {w : ℕ} : Garden w → Garden w → Type
  | refl (G : Garden w) : ReductionTrace G G
  | opA (G : Garden w) (hG : G.IsPlain) (b c : GBranch G.tree) (k : MiniCplCode)
      (h : MiniAOccurrence G b c k) : ReductionTrace G (collapseCoupleGarden (h.isSubCouple hG))
  | opB (G : Garden w) (hG : G.IsPlain) (b c : GBranch G.tree) (k : MiniTreeCode)
      (h : MiniBOccurrence G b c k) : ReductionTrace G (collapsePairedTreeGarden (h.isSubPairedTree hG))
  | trans {G H K : Garden w} : ReductionTrace G H → ReductionTrace H K → ReductionTrace G K

/-- Every target branch retains exactly its original ambient branch identity. -/
noncomputable def ReductionTrace.branches {w : ℕ} {G H : Garden w} (T : ReductionTrace G H) :
    GBranch H.tree ↪ GBranch G.tree :=
  match T with
  | .refl _ => Function.Embedding.refl _
  | .opA _ hG _ _ _ h => collapseCoupleBranchEmbedding (h.isSubCouple hG)
  | .opB _ hG _ _ _ h => collapsePairedTreeBranchEmbedding (h.isSubPairedTree hG)
  | .trans U V => V.branches.trans U.branches

theorem ReductionTrace.reduces {w : ℕ} {G H : Garden w} (T : ReductionTrace G H) : GardenReduces G H := by
  induction T with
  | refl => exact Relation.ReflTransGen.refl
  | opA G hG b c k h => exact Relation.ReflTransGen.single (GardenStep.opA G hG b c k h)
  | opB G hG b c k h => exact Relation.ReflTransGen.single (GardenStep.opB G hG b c k h)
  | trans U V ihU ihV => exact ihU.trans ihV

end WaveTurbulence.Reg.Skeleton
