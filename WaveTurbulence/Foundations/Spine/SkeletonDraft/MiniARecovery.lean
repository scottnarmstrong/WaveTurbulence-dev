/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniACollapse
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniAPairs
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapsedCouplePairs
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CarrierRoundTrip

/-! # Literal inverse A surgery on ordinary source gardens -/

public section
namespace WaveTurbulence.Reg.Skeleton
namespace MiniAOccurrence

/-- Actual A collapse and reinsertion recover the full ordered forest and canonical matching. -/
theorem recover_raw {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {k : MiniCplCode}
    (h : MiniAOccurrence G b c k) (hG : G.IsPlain) (hb : nodeSign G.sig b.1 = 1) :
    (rawOfGarden (collapseCoupleGarden (h.isSubCouple hG))).opA b.1 c.1 k = rawOfGarden G := by
  classical
  apply Raw.ext
  · rfl
  · exact h.recover_forest hG
  · change (sourcePairs (collapseCoupleGarden (h.isSubCouple hG))).erase (b.1,c.1) ∪ _ = sourcePairs G
    have he := collapseCoupleGarden_pairs_erase (h.isSubCouple hG) hb
    change (sourcePairs (collapseCoupleGarden (h.isSubCouple hG))).erase (b.1,c.1) = _ at he
    rw [he,← h.removed_pairs hG hb]
    have hf : (sourcePairs G).filter (fun p => ∃ ℓ : OutsideRoots G.tree b.toNode c.toNode, ℓ.1.1 = p.1) =
        (sourcePairs G).filter (fun p => ∃ ℓ : GLeaf G.tree,
          ℓ.1 = p.1 ∧ ℓ ∉ b.toNode.leavesBelow ∪ c.toNode.leavesBelow) := by
      apply Finset.filter_congr
      intro p hp
      constructor
      · rintro ⟨ℓ,hℓ⟩
        refine ⟨ℓ.1,hℓ,?_⟩
        simpa only [Finset.mem_union,leafBelow_iff_below,not_or] using ℓ.2
      · rintro ⟨ℓ,hℓ,hm⟩
        refine ⟨⟨ℓ,?_⟩,hℓ⟩
        simpa only [Finset.mem_union,leafBelow_iff_below,not_or] using hm
    rw [hf]
    exact sourcePairs_partition G hG _

/-- A positive-first actual A mini has an actual source predecessor. -/
theorem predecessor {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {k : MiniCplCode}
    (h : MiniAOccurrence G b c k) (hG : G.IsPlain) (hb : nodeSign G.sig b.1 = 1) :
    Expand (rawOfGarden (collapseCoupleGarden (h.isSubCouple hG))) (rawOfGarden G) := by
  rw [← h.recover_raw hG hb]
  apply Expand.opA
  · exact rawOfGarden_valid _ (collapseCoupleGarden_plain _ hG)
  · exact collapseCoupleGarden_root_pair (h.isSubCouple hG) hb

end MiniAOccurrence
end WaveTurbulence.Reg.Skeleton
