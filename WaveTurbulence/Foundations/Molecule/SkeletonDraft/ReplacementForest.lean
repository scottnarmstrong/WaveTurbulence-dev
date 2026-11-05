/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementBranches

/-! # Literal forest leaf and branch addresses after replacing an actual source node -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Exact old-outside / framed-new leaf decomposition, at arbitrary forest width. -/
theorem replaceNodeForest_leaf_iff {w : ℕ} (tree : Fin w → TTree) (a : GNode tree) (S : TTree) (x : Address w) :
    x.2 ∈ (Comb.replaceNodeForest tree a S x.1).leaves ↔
      (x.2 ∈ (tree x.1).leaves ∧ ¬ Below a.1 x) ∨ ∃ p : Path, p ∈ S.leaves ∧ x = addrExt a.1 p := by
  obtain ⟨j,p⟩ := x
  by_cases hj : j = a.1.1
  · have hf : Comb.replaceNodeForest tree a S j = Comb.replaceAt (tree a.1.1) a.1.2 S := by
      rw [Comb.replaceNodeForest,hj,Function.update_self]
    rw [hf,Comb.leaves_replaceAt_eq (Comb.nodeSubtree_spec a) S]
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with ho | hn
      · obtain ⟨hl,hp⟩ := Finset.mem_filter.mp ho
        exact Or.inl ⟨by rw [hj]; exact hl,fun h => hp h.2⟩
      · obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hn
        exact Or.inr ⟨r,hr,Prod.ext hj he.symm⟩
    · rintro (⟨hl,hn⟩ | ⟨r,hr,he⟩)
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨by rw [← hj]; exact hl,fun hp => hn ⟨hj,hp⟩⟩
      · apply Finset.mem_union_right
        have hv := congrArg (fun z : Address w => z.2) he
        exact Finset.mem_image.mpr ⟨r,hr,hv.symm⟩
  · have hf : Comb.replaceNodeForest tree a S j = tree j := by
      rw [Comb.replaceNodeForest,Function.update_of_ne hj]
    rw [hf]
    constructor
    · intro hp
      exact Or.inl ⟨hp,fun h => hj h.1⟩
    · rintro (⟨hp,_⟩ | ⟨r,hr,he⟩)
      · exact hp
      · have hv := congrArg (fun z : Address w => z.1) he
        exact (hj hv).elim

/-- Exact old-outside / framed-new branch decomposition, at arbitrary forest width. -/
theorem replaceNodeForest_branch_iff {w : ℕ} (tree : Fin w → TTree) (a : GNode tree) (S : TTree) (x : Address w) :
    x.2 ∈ (Comb.replaceNodeForest tree a S x.1).branching ↔
      (x.2 ∈ (tree x.1).branching ∧ ¬ Below a.1 x) ∨ ∃ p : Path, p ∈ S.branching ∧ x = addrExt a.1 p := by
  obtain ⟨j,p⟩ := x
  by_cases hj : j = a.1.1
  · have hf : Comb.replaceNodeForest tree a S j = Comb.replaceAt (tree a.1.1) a.1.2 S := by
      rw [Comb.replaceNodeForest,hj,Function.update_self]
    rw [hf,branching_replaceAt_eq (Comb.nodeSubtree_spec a) S]
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with ho | hn
      · obtain ⟨hl,hp⟩ := Finset.mem_filter.mp ho
        exact Or.inl ⟨by rw [hj]; exact hl,fun h => hp h.2⟩
      · obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hn
        exact Or.inr ⟨r,hr,Prod.ext hj he.symm⟩
    · rintro (⟨hl,hn⟩ | ⟨r,hr,he⟩)
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨by rw [← hj]; exact hl,fun hp => hn ⟨hj,hp⟩⟩
      · apply Finset.mem_union_right
        have hv := congrArg (fun z : Address w => z.2) he
        exact Finset.mem_image.mpr ⟨r,hr,hv.symm⟩
  · have hf : Comb.replaceNodeForest tree a S j = tree j := by
      rw [Comb.replaceNodeForest,Function.update_of_ne hj]
    rw [hf]
    constructor
    · intro hp
      exact Or.inl ⟨hp,fun h => hj h.1⟩
    · rintro (⟨hp,_⟩ | ⟨r,hr,he⟩)
      · exact hp
      · have hv := congrArg (fun z : Address w => z.1) he
        exact (hj hv).elim

end WaveTurbulence.Reg.Skeleton
