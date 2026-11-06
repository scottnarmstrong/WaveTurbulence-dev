/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawAForestRecovery
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardAMini
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniARecovery
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.GardenReduction

/-! # Collapsing the mini created by source A returns the exact original source object -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem MiniAOccurrence.collapsed_raw_eq_of_expansion {w : ℕ} {G : Garden w}
    {b c : GBranch G.tree} {k : MiniCplCode} (h : MiniAOccurrence G b c k) (hG : G.IsPlain)
    (hb : nodeSign G.sig b.1 = 1) (R : Raw w) (hR : R.Valid) (hp : (b.1,c.1) ∈ R.pairs)
    (he : rawOfGarden G = R.opA b.1 c.1 k) :
    rawOfGarden (collapseCoupleGarden (h.isSubCouple hG)) = R := by
  have hn := rawOfGarden_valid _ (collapseCoupleGarden_plain (h.isSubCouple hG) hG)
  have hpair := collapseCoupleGarden_root_pair (h.isSubCouple hG) hb
  exact Raw.opA_injective_at _ R hn hR b.1 c.1 k hpair hp ((h.recover_raw hG hb).trans he)

theorem gardenStep_of_raw_opA {w : ℕ} (S G : Garden w) (hS : S.IsPlain) (hG : G.IsPlain)
    (x y : Address w) (k : MiniCplCode) (hp : (x,y) ∈ (rawOfGarden S).pairs)
    (he : rawOfGarden G = (rawOfGarden S).opA x y k) : GardenStep G S := by
  have hv := rawOfGarden_valid S hS
  obtain ⟨b,c,hb,hc,hm⟩ := sourceMiniA_of_raw_opA (rawOfGarden S) hv G x y k hp he
  have hsig := congrArg Raw.sig he
  change G.sig = S.sig at hsig
  have hpos : nodeSign G.sig b.1 = 1 := by
    rw [hb,hsig]
    exact (hv.1 _ hp).2.2.1
  have hn : (b.1,c.1) ∈ (rawOfGarden S).pairs := by rw [hb,hc]; exact hp
  have he' : rawOfGarden G = (rawOfGarden S).opA b.1 c.1 k := by rw [hb,hc]; exact he
  have hr := hm.collapsed_raw_eq_of_expansion hG hpos (rawOfGarden S) hv hn he'
  have hg : collapseCoupleGarden (hm.isSubCouple hG) = S :=
    rawOfGarden_injective_plain (collapseCoupleGarden_plain _ hG) hS hr
  exact hg ▸ GardenStep.opA G hG b c k hm

end WaveTurbulence.Reg.Skeleton
