/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReductionTrace

/-! # Graph histories with the exact inherited labels computed by actual surgery traces -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReductionTrace.graph_reduces {w : ℕ} {G H : Garden w} (T : ReductionTrace G H)
    {B : Type*} [DecidableEq B] (label : GBranch G.tree ↪ B) :
    PortMatching.Reduces (LabelledGarden.mk G label).graph
      (LabelledGarden.mk H (T.branches.trans label)).graph := by
  induction T with
  | refl => exact Relation.ReflTransGen.refl
  | opA G hG b c k h =>
    exact Relation.ReflTransGen.single ((LabelledGarden.mk G label).miniA_graph_step h hG)
  | opB G hG b c k h =>
    exact Relation.ReflTransGen.single ((LabelledGarden.mk G label).miniB_graph_step h hG)
  | trans U V ihU ihV => exact (ihU label).trans (ihV (U.branches.trans label))

end WaveTurbulence.Reg.Skeleton
