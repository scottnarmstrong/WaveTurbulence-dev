/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cumulant.Products

/-!
# Lifting partitions through disjoint nonempty groups

Finite partition infrastructure for TARGET Lemma `propertycm`.
-/

public section

namespace WaveTurbulence.CumulantProducts
open scoped Classical

/-- Union over disjoint nonempty groups reflects inclusion of subfamilies. -/
theorem biUnion_groups_subset_iff {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) {A B : Finset ι} (hA : A ⊆ I) (hB : B ⊆ I) :
    A.biUnion S ⊆ B.biUnion S ↔ A ⊆ B := by
  constructor
  · intro h i hi
    obtain ⟨j, hj⟩ := hne i (hA hi)
    obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp (h (Finset.mem_biUnion.mpr ⟨i, hi, hj⟩))
    exact index_eq_of_mem_groups hS (hA hi) (hB hk) hj hjk ▸ hk
  · intro h j hj
    obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
    exact Finset.mem_biUnion.mpr ⟨i, h hi, hji⟩

/-- Replace each block of group indices by the union of its groups. -/
@[expose] noncomputable def groupPartition {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (I : Finset ι) (S : ι → Finset J) (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) (Q : Finpartition I) : Finpartition (I.biUnion S) where
  parts := Q.parts.image (fun A => A.biUnion S)
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro U hU V hV hneUV
    obtain ⟨A, hApart, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨B, hBpart, rfl⟩ := Finset.mem_image.mp hV
    have hAB : A ≠ B := fun h => hneUV (congrArg (fun C => C.biUnion S) h)
    exact disjoint_biUnion_groups hS (Q.le hApart) (Q.le hBpart) (Q.disjoint hApart hBpart hAB)
  sup_parts := by
    ext j
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨U, hU, hj⟩
      obtain ⟨A, hApart, rfl⟩ := Finset.mem_image.mp hU
      obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
      exact Finset.mem_biUnion.mpr ⟨i, Q.le hApart hi, hji⟩
    · intro hj
      obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
      refine ⟨(Q.part i).biUnion S,
        Finset.mem_image.mpr ⟨Q.part i, Q.part_mem.mpr hi, rfl⟩, ?_⟩
      exact Finset.mem_biUnion.mpr ⟨i, Q.mem_part hi, hji⟩
  bot_notMem := by
    intro h
    obtain ⟨A, hA, he⟩ := Finset.mem_image.mp h
    obtain ⟨i, hi⟩ := Q.nonempty_of_mem_parts hA
    obtain ⟨j, hj⟩ := hne i (Q.le hA hi)
    have hm : j ∈ A.biUnion S := Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
    rw [he] at hm
    exact Finset.notMem_empty j hm

/-- The blocks of a lifted partition. -/
theorem groupPartition_parts {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (I : Finset ι) (S : ι → Finset J) (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) (Q : Finpartition I) :
    (groupPartition I S hS hne Q).parts = Q.parts.image (fun A => A.biUnion S) := rfl

/-- Lifting disjoint nonempty groups preserves the number of blocks. -/
theorem groupPartition_card {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (I : Finset ι) (S : ι → Finset J) (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) (Q : Finpartition I) :
    (groupPartition I S hS hne Q).parts.card = Q.parts.card := by
  rw [groupPartition_parts, Finset.card_image_iff]
  intro A hA B hB hAB
  exact biUnion_groups_injective hS hne (Q.le hA) (Q.le hB) hAB

/-- Refinement between lifted group partitions is exactly refinement of their group indices. -/
theorem groupPartition_le_iff {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (I : Finset ι) (S : ι → Finset J) (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) (Q R : Finpartition I) :
    groupPartition I S hS hne Q ≤ groupPartition I S hS hne R ↔ Q ≤ R := by
  constructor
  · intro h A hA
    obtain ⟨C, hC, hAC⟩ := h (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨B, hB, (biUnion_groups_subset_iff hS hne (Q.le hA) (R.le hB)).mp hAC⟩
  · intro h U hU
    obtain ⟨A, hApart, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨B, hB, hAB⟩ := h hApart
    exact ⟨B.biUnion S, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
      (biUnion_groups_subset_iff hS hne (Q.le hApart) (R.le hB)).mpr hAB⟩

/-- Lifting through disjoint nonempty groups is injective. -/
theorem groupPartition_injective {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (I : Finset ι) (S : ι → Finset J) (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) : Function.Injective (groupPartition I S hS hne) := by
  intro Q R h
  exact le_antisymm ((groupPartition_le_iff I S hS hne Q R).mp h.le)
    ((groupPartition_le_iff I S hS hne R Q).mp h.ge)

end WaveTurbulence.CumulantProducts
