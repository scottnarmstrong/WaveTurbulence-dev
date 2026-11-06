/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBBranchRegion
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.PairedTreeBranchRange

/-! # Exact surviving branch labels for actual source B-mini collapse -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree
namespace MiniBOccurrence

theorem branch_survives_iff {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (d : GBranch G.tree) :
    (¬ Below b.1 d.1 ∨ Below (c.child m.lone).1 d.1) ↔ d ≠ b ∧ d ≠ c := by
  have hc : c.1 = addrExt b.1 [m.c] := (congrArg (fun a : GNode G.tree => a.1) h.1).symm
  have hbc : Below b.1 c.1 := by rw [hc]; exact below_extend b.1 [m.c]
  have hbb : Below b.1 b.1 := ⟨rfl,List.prefix_refl _⟩
  have hlb : ¬ Below (c.child m.lone).1 b.1 := by
    intro he
    have hh := he.2.length_le
    rw [h.lone_frame] at hh
    change (b.1.2 ++ [m.c,m.lone]).length ≤ b.1.2.length at hh
    simp only [List.length_append,List.length_cons,List.length_nil] at hh
    omega
  have hlc : ¬ Below (c.child m.lone).1 c.1 := by
    intro he
    have hh := he.2.length_le
    change (c.1.2 ++ [m.lone]).length ≤ c.1.2.length at hh
    simp only [List.length_append,List.length_singleton] at hh
    omega
  constructor
  · intro hs
    constructor
    · rintro rfl
      exact hs.elim (fun he => he hbb) hlb
    · rintro rfl
      exact hs.elim (fun he => he hbc) hlc
  · rintro ⟨hdb,hdc⟩
    by_cases hd : Below b.1 d.1
    · right
      obtain ⟨p,hp⟩ := below_exists_frame b.1 d.1 hd
      have hm : p ∈ (Comb.nodeSubtree b.toNode).branching := by
        apply (Comb.subtree_branching_iff (Comb.nodeSubtree_spec b.toNode) p).mpr
        change (addrExt b.1 p).2 ∈ (G.tree (addrExt b.1 p).1).branching
        rw [← hp]
        exact d.2
      rw [h.upper_tree] at hm
      rcases miniContext_branch_cases m _ p hm with he | he | he
      · exact (hdb (Subtype.ext (by rw [hp,he]; exact Prod.ext rfl (List.append_nil _)))).elim
      · exact (hdc (Subtype.ext (hp.trans (by rw [he,← hc])))).elim
      · rw [h.lone_frame,hp]
        exact (below_frames_iff b.1 [m.c,m.lone] p).mpr he
    · exact Or.inl hd

theorem branch_embedding_range {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (hG : G.IsPlain) (d : GBranch G.tree) :
    d ∈ Set.range (collapsePairedTreeBranchEmbedding (h.isSubPairedTree hG)) ↔ d ≠ b ∧ d ≠ c := by
  rw [collapsePairedTreeBranchEmbedding_range]
  exact h.branch_survives_iff d

end MiniBOccurrence
end WaveTurbulence.Reg.Skeleton
