/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SubforestBranches
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PrefixStretch

/-! # Exact actual branch range of a rooted subforest and an embedded subcouple -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem subforestBranchEmbedding_range {w v : ℕ} {tree : Fin w → TTree}
    (E : Comb.RootedSubforest tree v) (d : GBranch tree) :
    d ∈ Set.range (subforestBranchEmbedding E) ↔ ∃ j : Fin v, Below (E.root j).1 d.1 := by
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨b.1.1,rfl,List.prefix_append _ _⟩
  · rintro ⟨j,hj⟩
    obtain ⟨p,hp⟩ := below_exists_frame (E.root j).1 d.1 hj
    have hb : p ∈ (E.shape j).branching := by
      apply (Comb.subtree_branching_iff (E.subtree_eq j) p).mpr
      change (addrExt (E.root j).1 p).2 ∈ (tree (addrExt (E.root j).1 p).1).branching
      rw [← hp]
      exact d.2
    refine ⟨⟨(j,p),hb⟩,?_⟩
    apply Subtype.ext
    exact hp.symm

theorem subcoupleBranchEmbedding_range {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (hab : Comb.IsSubCouple G a b) (d : GBranch G.tree) :
    d ∈ Set.range (subforestBranchEmbedding (Comb.twoRootSubforest a b (Comb.subCouple_incomparable hab))) ↔
      Below a.1 d.1 ∨ Below b.1 d.1 := by
  rw [subforestBranchEmbedding_range]
  constructor
  · rintro ⟨j,hj⟩
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr hj
  · rintro (ha | hb)
    · exact ⟨0,ha⟩
    · exact ⟨1,hb⟩

end WaveTurbulence.Reg.Skeleton
