/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBCollapse
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBPairs
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CarrierRoundTrip

/-! # Literal inverse B surgery on ordinary source gardens -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree
namespace MiniBOccurrence

/-- Collapsing an actual B mini and reinserting its same code restores all literal forest/pair data. -/
theorem recover_raw {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (hG : G.IsPlain) :
    (rawOfGarden (collapsePairedTreeGarden (h.isSubPairedTree hG))).opB b.1 m = rawOfGarden G := by
  apply Raw.ext
  · rfl
  · exact h.recover_forest hG
  · change (sourcePairs (collapsePairedTreeGarden (h.isSubPairedTree hG))).image
      (fun p => (relocate b.1 m.c m.lone p.1,relocate b.1 m.c m.lone p.2)) ∪
        miniPairs G.sig b.1 m = sourcePairs G
    simp only [relocate_eq_stretch]
    rw [← h.collapse_path hG]
    have ht := collapsePairedTreeGarden_pairs (h.isSubPairedTree hG)
    change (sourcePairs (collapsePairedTreeGarden (h.isSubPairedTree hG))).image
      (fun p => (stretch b.1 (Comb.collapseDataOfDesc (h.isSubPairedTree hG).1).path p.1,
        stretch b.1 (Comb.collapseDataOfDesc (h.isSubPairedTree hG).1).path p.2)) = _ at ht
    rw [ht]
    rw [← h.removed_pairs hG]
    exact sourcePairs_partition G hG _

/-- The collapsed source B mini is a genuine predecessor under the source expansion relation. -/
theorem predecessor {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (hG : G.IsPlain) :
    Expand (rawOfGarden (collapsePairedTreeGarden (h.isSubPairedTree hG))) (rawOfGarden G) := by
  rw [← h.recover_raw hG]
  apply Expand.opB
  · exact rawOfGarden_valid _ (collapsePairedTreeGarden_plain _ hG)
  · exact (Comb.subtree_exists_iff _ _).mp ⟨_,h.collapsed_subtree hG⟩

end MiniBOccurrence
end WaveTurbulence.Reg.Skeleton
