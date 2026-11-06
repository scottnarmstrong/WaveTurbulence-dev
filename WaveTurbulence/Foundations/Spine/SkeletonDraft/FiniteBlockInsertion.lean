/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # Finite unions of transported blocks with a shared inserted pair set -/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- A local insertion shared by any nonempty collection of active blocks appears once globally. -/
theorem biUnion_image_insertion {ι α β : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] [DecidableEq β] (P : ι → Finset α) (Q : ι → Finset β)
    (f : α → β) (active : ι → Prop) [DecidablePred active] (K : Finset β)
    (h : ∀ i, Q i = (P i).image f ∪ if active i then K else ∅)
    (ha : ∃ i, active i) :
    Finset.univ.biUnion Q = (Finset.univ.biUnion P).image f ∪ K := by
  ext z
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image,
    Finset.mem_union]
  constructor
  · rintro ⟨i,hi⟩
    rw [h i] at hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨x,hx,hz⟩ := Finset.mem_image.mp hi
      exact Or.inl ⟨x,⟨i,hx⟩,hz⟩
    · exact Or.inr (by split_ifs at hi with hac; exact hi; simp at hi)
  · rintro (⟨x,⟨i,hx⟩,hz⟩ | hk)
    · refine ⟨i,?_⟩
      rw [h i]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x,hx,hz⟩)
    · obtain ⟨i,hi⟩ := ha
      refine ⟨i,?_⟩
      rw [h i,if_pos hi]
      exact Finset.mem_union_right _ hk

end WaveTurbulence.Reg.Skeleton
