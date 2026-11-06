/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReductionTrace
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawBOrdinaryPredecessor

/-! # Actual B predecessor trace retains every old branch at its exact relocated address -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem exists_predecessor_trace_of_raw_opB {w : ℕ} (R : Raw w) (G : Garden w)
    (hG : G.IsPlain) (a : Address w) (m : MiniTreeCode)
    (ha : a.2 ∈ (R.tree a.1).nodes) (he : rawOfGarden G = R.opB a m) :
    ∃ H : Garden w, H.IsPlain ∧ rawOfGarden H = R ∧
      ∃ T : ReductionTrace G H, ∀ b : GBranch H.tree,
        (T.branches b).1 = relocate a m.c m.lone b.1 := by
  obtain ⟨b,c,hb,hc,hm⟩ := sourceMiniB_of_raw_opB R G a m ha he
  have hn : b.1.2 ∈ (R.tree b.1.1).nodes := by rw [hb]; exact ha
  have he' : rawOfGarden G = R.opB b.1 m := by rw [hb]; exact he
  refine ⟨collapsePairedTreeGarden (hm.isSubPairedTree hG),
    collapsePairedTreeGarden_plain _ hG,hm.collapsed_raw_eq_of_expansion hG R hn he',
    ReductionTrace.opB G hG b c m hm,?_⟩
  intro d
  change stretch b.1 (Comb.collapseDataOfDesc (hm.isSubPairedTree hG).1).path d.1 = _
  rw [hm.collapse_path hG,hb]
  rfl

end WaveTurbulence.Reg.Skeleton
