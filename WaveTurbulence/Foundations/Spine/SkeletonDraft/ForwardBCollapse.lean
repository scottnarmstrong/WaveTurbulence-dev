/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawBForestRecovery
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBRecovery
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GardenReduction
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardBMini

/-! # Collapsing the mini created by source B returns the exact original source object -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem MiniBOccurrence.collapsed_raw_eq_of_expansion {w : ℕ} {G : Garden w}
    {b c : GBranch G.tree} {m : MiniTreeCode} (h : MiniBOccurrence G b c m) (hG : G.IsPlain)
    (R : Raw w) (ha : b.1.2 ∈ (R.tree b.1.1).nodes) (he : rawOfGarden G = R.opB b.1 m) :
    rawOfGarden (collapsePairedTreeGarden (h.isSubPairedTree hG)) = R := by
  have hn : b.1.2 ∈ ((rawOfGarden (collapsePairedTreeGarden (h.isSubPairedTree hG))).tree b.1.1).nodes :=
    (Comb.subtree_exists_iff _ _).mp ⟨_,h.collapsed_subtree hG⟩
  exact Raw.opB_injective_at _ R b.1 m hn ha ((h.recover_raw hG).trans he)

theorem gardenStep_of_raw_opB {w : ℕ} (S G : Garden w) (hS : S.IsPlain) (hG : G.IsPlain)
    (a : Address w) (m : MiniTreeCode) (ha : a.2 ∈ (S.tree a.1).nodes)
    (he : rawOfGarden G = (rawOfGarden S).opB a m) : GardenStep G S := by
  obtain ⟨b,c,hb,hc,hm⟩ := sourceMiniB_of_raw_opB (rawOfGarden S) G a m ha he
  have hn : b.1.2 ∈ (S.tree b.1.1).nodes := by rw [hb]; exact ha
  have he' : rawOfGarden G = (rawOfGarden S).opB b.1 m := by rw [hb]; exact he
  have hr := hm.collapsed_raw_eq_of_expansion hG (rawOfGarden S) hn he'
  have hg : collapsePairedTreeGarden (hm.isSubPairedTree hG) = S :=
    rawOfGarden_injective_plain (collapsePairedTreeGarden_plain _ hG) hS hr
  exact hg ▸ GardenStep.opB G hG b c m hm

end WaveTurbulence.Reg.Skeleton
