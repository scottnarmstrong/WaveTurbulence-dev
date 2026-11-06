/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # Pair substitution distributes over the complete finite union of code blocks -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem biUnion_pair_substitution {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (P Q : ι → Finset α) (x : α) (K : Finset α)
    (h : ∀ i z, z ∈ Q i ↔ (z ∈ P i ∧ z ≠ x) ∨ (x ∈ P i ∧ z ∈ K)) :
    Finset.univ.biUnion Q = (Finset.univ.biUnion P).erase x ∪
      (if x ∈ Finset.univ.biUnion P then K else ∅) := by
  by_cases hx : x ∈ Finset.univ.biUnion P
  · rw [ite_eq_left hx]
    ext z
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_erase,h]
    have hex : ∃ i, x ∈ P i := by simpa using hx
    constructor
    · rintro ⟨i,hi | hi⟩
      · exact Or.inl ⟨hi.2,i,hi.1⟩
      · exact Or.inr hi.2
    · rintro (⟨hn,i,hi⟩ | hk)
      · exact ⟨i,Or.inl ⟨hi,hn⟩⟩
      · obtain ⟨i,hi⟩ := hex
        exact ⟨i,Or.inr ⟨hi,hk⟩⟩
  · rw [ite_eq_right hx]
    ext z
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_erase,h,
      Finset.notMem_empty,or_false]
    have hn : ∀ i, x ∉ P i := by
      intro i hi
      exact hx (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩)
    constructor
    · rintro ⟨i,hi | hi⟩
      · exact ⟨hi.2,i,hi.1⟩
      · exact (hn i hi.1).elim
    · rintro ⟨hz,i,hi⟩
      exact ⟨i,Or.inl ⟨hi,hz⟩⟩

end WaveTurbulence.Reg.Skeleton
