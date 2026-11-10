/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniARecovery
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBRecovery
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.Order

/-! # Literal source garden reduction by inverse A/B mini surgery -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- One source inverse surgery, at an actual embedded A or B mini. -/
inductive GardenStep {w : ℕ} : Garden w → Garden w → Prop
  | opA (G : Garden w) (hG : G.IsPlain) (b c : GBranch G.tree) (k : MiniCplCode)
      (h : MiniAOccurrence G b c k) : GardenStep G (collapseCoupleGarden (h.isSubCouple hG))
  | opB (G : Garden w) (hG : G.IsPlain) (b c : GBranch G.tree) (k : MiniTreeCode)
      (h : MiniBOccurrence G b c k) : GardenStep G (collapsePairedTreeGarden (h.isSubPairedTree hG))

/-- A finite source reduction history, retaining the full actual Garden carrier. -/
def GardenReduces {w : ℕ} : Garden w → Garden w → Prop := Relation.ReflTransGen GardenStep

theorem GardenStep.sig_eq {w : ℕ} {G H : Garden w} (h : GardenStep G H) : H.sig = G.sig := by
  cases h <;> rfl

theorem GardenReduces.sig_eq {w : ℕ} {G H : Garden w} (h : GardenReduces G H) : H.sig = G.sig := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact hs.sig_eq.trans ih

end WaveTurbulence.Reg.Skeleton
