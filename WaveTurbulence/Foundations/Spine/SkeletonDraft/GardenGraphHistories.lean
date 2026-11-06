/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GardenReduction
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniAGraphCollapse
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBGraphCollapse

/-! # Every actual garden reduction history retains exact original branch labels -/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- A source step transports any injective original branch labels and gives its actual graph step. -/
theorem GardenStep.lift {w : ℕ} {B : Type*} [DecidableEq B] {G H : Garden w}
    (h : GardenStep G H) (label : GBranch G.tree ↪ B) :
    ∃ label' : GBranch H.tree ↪ B,
      PortMatching.Step (LabelledGarden.mk G label).graph (LabelledGarden.mk H label').graph := by
  cases h with
  | opA hG b c k hm =>
    let S : LabelledGarden w B := ⟨G,label⟩
    exact ⟨(S.collapseCouple (hm.isSubCouple hG)).label,S.miniA_graph_step hm hG⟩
  | opB hG b c k hm =>
    let S : LabelledGarden w B := ⟨G,label⟩
    exact ⟨(S.collapsePairedTree (hm.isSubPairedTree hG)).label,S.miniB_graph_step hm hG⟩

/-- A finite actual A/B reduction history is a finite labelled graph history; labels are constructed,
not supplied as a graph-history hypothesis. -/
theorem GardenReduces.lift {w : ℕ} {B : Type*} [DecidableEq B] {G H : Garden w}
    (h : GardenReduces G H) (label : GBranch G.tree ↪ B) :
    ∃ label' : GBranch H.tree ↪ B,
      PortMatching.Reduces (LabelledGarden.mk G label).graph (LabelledGarden.mk H label').graph := by
  induction h with
  | refl => exact ⟨label,Relation.ReflTransGen.refl⟩
  | tail hr hs ih =>
    obtain ⟨labelH,hlabelH⟩ := ih
    obtain ⟨labelK,hlabelK⟩ := hs.lift labelH
    exact ⟨labelK,hlabelH.tail hlabelK⟩

end WaveTurbulence.Reg.Skeleton
