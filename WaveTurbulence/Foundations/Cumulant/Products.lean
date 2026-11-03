/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cumulant.Inversion

/-!
# Partitions for cumulants of products

TARGET Lemma `propertycm`, L2343–L2351. Irreducibility is stated literally in
terms of unions of blocks, with the author-approved corrections: the forbidden
subfamily is nonempty and proper, and the product groups in the identity are
nonempty. The latter is necessary for unnormalized restricted measures.
-/

public section

namespace WaveTurbulence

/-- Source irreducibility for TARGET Lemma `propertycm`: no nonempty proper
subfamily of groups has union equal to a union of partition blocks. -/
@[expose] def IsIrreduciblePartition {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    (I : Finset ι) (S : ι → Finset J) (P : Finpartition (I.biUnion S)) : Prop :=
  ∀ A ⊆ I, A.Nonempty → A ≠ I →
    ¬∃ B : Finset (Finset J), B ⊆ P.parts ∧ A.biUnion S = B.biUnion id

namespace CumulantProducts

/-- Two disjoint groups cannot contain the same position. -/
theorem index_eq_of_mem_groups {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (hS : (I : Set ι).PairwiseDisjoint S)
    {i k : ι} (hi : i ∈ I) (hk : k ∈ I) {j : J} (hji : j ∈ S i) (hjk : j ∈ S k) : i = k := by
  by_contra hik
  exact Finset.disjoint_left.mp (hS hi hk hik) hji hjk

/-- Unions of disjoint nonempty groups retain the subfamily of indices. -/
theorem biUnion_groups_injective {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (hS : (I : Set ι).PairwiseDisjoint S)
    (hne : ∀ i ∈ I, (S i).Nonempty) {A B : Finset ι} (hA : A ⊆ I) (hB : B ⊆ I)
    (he : A.biUnion S = B.biUnion S) : A = B := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨j, hj⟩ := hne i (hA hi)
    have hm : j ∈ B.biUnion S := he ▸ Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
    obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp hm
    exact index_eq_of_mem_groups hS (hA hi) (hB hk) hj hjk ▸ hk
  · intro i hi
    obtain ⟨j, hj⟩ := hne i (hB hi)
    have hm : j ∈ A.biUnion S := he.symm ▸ Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
    obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp hm
    exact index_eq_of_mem_groups hS (hB hi) (hA hk) hj hjk ▸ hk

/-- For disjoint groups, union over a subfamily preserves intersections. -/
theorem biUnion_groups_inter {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (hS : (I : Set ι).PairwiseDisjoint S)
    {A B : Finset ι} (hA : A ⊆ I) (hB : B ⊆ I) :
    (A ∩ B).biUnion S = A.biUnion S ∩ B.biUnion S := by
  ext j
  simp only [Finset.mem_biUnion, Finset.mem_inter]
  constructor
  · rintro ⟨i, ⟨hiA, hiB⟩, hji⟩
    exact ⟨⟨i, hiA, hji⟩, ⟨i, hiB, hji⟩⟩
  · rintro ⟨⟨i, hi, hji⟩, ⟨k, hk, hjk⟩⟩
    have hik := index_eq_of_mem_groups hS (hA hi) (hB hk) hji hjk
    subst k
    exact ⟨i, ⟨hi, hk⟩, hji⟩

/-- Disjoint subfamilies of disjoint groups have disjoint unions. -/
theorem disjoint_biUnion_groups {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (hS : (I : Set ι).PairwiseDisjoint S)
    {A B : Finset ι} (hA : A ⊆ I) (hB : B ⊆ I) (hAB : Disjoint A B) :
    Disjoint (A.biUnion S) (B.biUnion S) := by
  apply Finset.disjoint_left.mpr
  intro j hjA hjB
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hjA
  obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp hjB
  have hik := index_eq_of_mem_groups hS (hA hi) (hB hk) hji hjk
  subst k
  exact Finset.disjoint_left.mp hAB hi hk

end CumulantProducts
end WaveTurbulence

namespace WaveTurbulence.CumulantProducts
open scoped Classical

/-- Every fine block lies in the union of the groups of one coarse block. -/
@[expose] def RespectsGroups {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} (S : ι → Finset J) (P : Finpartition (I.biUnion S))
    (Q : Finpartition I) : Prop :=
  ∀ B ∈ P.parts, ∃ A ∈ Q.parts, B ⊆ A.biUnion S

/-- Passing to a coarser partition of the groups preserves compatibility. -/
theorem RespectsGroups.mono {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} {P : Finpartition (I.biUnion S)}
    {Q R : Finpartition I} (hQ : RespectsGroups S P Q) (hQR : Q ≤ R) :
    RespectsGroups S P R := by
  intro B hB
  obtain ⟨A, hA, hBA⟩ := hQ B hB
  obtain ⟨C, hC, hAC⟩ := hQR hA
  refine ⟨C, hC, ?_⟩
  intro j hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp (hBA hj)
  exact Finset.mem_biUnion.mpr ⟨i, hAC hi, hji⟩

/-- The one-block coarse partition always respects the fine partition. -/
theorem respectsGroups_top {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} (S : ι → Finset J) (P : Finpartition (I.biUnion S)) :
    RespectsGroups S P ⊤ := by
  intro B hB
  obtain ⟨j, hj⟩ := P.nonempty_of_mem_parts hB
  obtain ⟨i, hi, _⟩ := Finset.mem_biUnion.mp (P.le hB hj)
  have hI : I ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨i, hi⟩
  obtain ⟨A, hA⟩ := (⊤ : Finpartition I).parts_nonempty hI
  have hAI : A = I := Finset.mem_singleton.mp (Finpartition.parts_top_subset I hA)
  subst A
  exact ⟨I, hA, P.le hB⟩

/-- Compatibility is closed under common refinement when the groups are disjoint. -/
theorem respectsGroups_inf {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (hS : (I : Set ι).PairwiseDisjoint S)
    (P : Finpartition (I.biUnion S)) {Q R : Finpartition I}
    (hQ : RespectsGroups S P Q) (hR : RespectsGroups S P R) :
    RespectsGroups S P (Q ⊓ R) := by
  intro B hB
  obtain ⟨A, hA, hBA⟩ := hQ B hB
  obtain ⟨C, hC, hBC⟩ := hR B hB
  have hsub : B ⊆ (A ∩ C).biUnion S := by
    rw [biUnion_groups_inter hS (Q.le hA) (R.le hC)]
    exact Finset.subset_inter hBA hBC
  obtain ⟨j, hj⟩ := P.nonempty_of_mem_parts hB
  obtain ⟨i, hi, _⟩ := Finset.mem_biUnion.mp (hsub hj)
  have hAC : A ∩ C ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨i, hi⟩
  refine ⟨A ∩ C, ?_, hsub⟩
  rw [Finpartition.parts_inf, Finset.mem_erase]
  exact ⟨hAC, Finset.mem_image.mpr ⟨(A, C), Finset.mem_product.mpr ⟨hA, hC⟩, rfl⟩⟩

/-- Compatibility is closed under every finite common refinement. -/
theorem respectsGroups_finset_inf {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (hS : (I : Set ι).PairwiseDisjoint S)
    (P : Finpartition (I.biUnion S)) (T : Finset (Finpartition I))
    (hT : ∀ Q ∈ T, RespectsGroups S P Q) : RespectsGroups S P (T.inf id) := by
  induction T using Finset.induction_on with
  | empty =>
    simpa only [Finset.inf_empty] using respectsGroups_top S P
  | @insert Q T hQT ih =>
    rw [Finset.inf_insert]
    exact respectsGroups_inf hS P (hT Q (Finset.mem_insert_self _ _))
      (ih (fun R hR => hT R (Finset.mem_insert_of_mem hR)))

/-- The coarsest equivalence generated on the groups by the fine blocks,
constructed as the common refinement of all respecting coarse partitions. -/
@[expose] noncomputable def groupComponentPartition {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} (S : ι → Finset J) (P : Finpartition (I.biUnion S)) : Finpartition I :=
  (Finset.univ.filter (RespectsGroups S P)).inf id

/-- The generated group-component partition itself respects every fine block. -/
theorem respectsGroups_groupComponentPartition {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (hS : (I : Set ι).PairwiseDisjoint S)
    (P : Finpartition (I.biUnion S)) : RespectsGroups S P (groupComponentPartition S P) :=
  respectsGroups_finset_inf hS P _ (fun _ hQ => (Finset.mem_filter.mp hQ).2)

/-- Every respecting coarse partition lies above the generated group components. -/
theorem groupComponentPartition_le {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (P : Finpartition (I.biUnion S))
    {Q : Finpartition I} (hQ : RespectsGroups S P Q) : groupComponentPartition S P ≤ Q :=
  Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩)

/-- Respecting coarse partitions are precisely the coarsenings of the group components. -/
theorem groupComponentPartition_le_iff {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (hS : (I : Set ι).PairwiseDisjoint S)
    (P : Finpartition (I.biUnion S)) (Q : Finpartition I) :
    groupComponentPartition S P ≤ Q ↔ RespectsGroups S P Q :=
  ⟨(respectsGroups_groupComponentPartition hS P).mono,
    groupComponentPartition_le P⟩

end WaveTurbulence.CumulantProducts

namespace WaveTurbulence.CumulantProducts
open scoped Classical

/-- Disjoint-group unions preserve relative complements. -/
theorem biUnion_groups_sdiff {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (hS : (I : Set ι).PairwiseDisjoint S)
    {A : Finset ι} (hA : A ⊆ I) :
    (I \ A).biUnion S = I.biUnion S \ A.biUnion S := by
  ext j
  simp only [Finset.mem_biUnion, Finset.mem_sdiff]
  constructor
  · rintro ⟨i, ⟨hi, hiA⟩, hji⟩
    refine ⟨⟨i, hi, hji⟩, ?_⟩
    rintro ⟨k, hk, hjk⟩
    have hik := index_eq_of_mem_groups hS hi (hA hk) hji hjk
    exact hiA (hik.symm ▸ hk)
  · rintro ⟨⟨i, hi, hji⟩, hnot⟩
    exact ⟨i, ⟨hi, fun hiA => hnot ⟨i, hiA, hji⟩⟩, hji⟩

/-- A block of a respecting group partition is a union of fine blocks. -/
theorem union_groups_eq_union_blocks {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (hS : (I : Set ι).PairwiseDisjoint S)
    (P : Finpartition (I.biUnion S)) {Q : Finpartition I} (hQ : RespectsGroups S P Q)
    {A : Finset ι} (hA : A ∈ Q.parts) :
    A.biUnion S = (P.parts.filter (fun B => B ⊆ A.biUnion S)).biUnion id := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
    have hjI : j ∈ I.biUnion S := Finset.mem_biUnion.mpr ⟨i, Q.le hA hi, hji⟩
    have hB := P.part_mem.mpr hjI
    obtain ⟨C, hC, hBC⟩ := hQ (P.part j) hB
    obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp (hBC (P.mem_part hjI))
    have hik := index_eq_of_mem_groups hS (Q.le hA hi) (Q.le hC hk) hji hjk
    have hAC : A = C := by
      by_contra hne
      exact Finset.disjoint_left.mp (Q.disjoint hA hC hne) hi (hik.symm ▸ hk)
    subst C
    exact Finset.mem_biUnion.mpr ⟨P.part j, Finset.mem_filter.mpr ⟨hB, hBC⟩, P.mem_part hjI⟩
  · intro hj
    obtain ⟨B, hB, hjB⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp hB).2 hjB

/-- A nontrivial partition of a nonempty set has a proper block. -/
theorem exists_proper_part_of_ne_top {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (Q : Finpartition I) (hI : I.Nonempty) (hQ : Q ≠ ⊤) : ∃ A ∈ Q.parts, A ≠ I := by
  by_contra h
  push Not at h
  apply hQ
  apply le_antisymm le_top
  intro B hB
  have hBI := Finset.mem_singleton.mp (Finpartition.parts_top_subset I hB)
  subst B
  obtain ⟨A, hA⟩ := Q.parts_nonempty (Finset.nonempty_iff_ne_empty.mp hI)
  exact ⟨A, hA, by rw [h A hA]⟩

/-- Irreducibility forces the generated group-component partition to have one block. -/
theorem groupComponentPartition_eq_top_of_irreducible {ι J : Type*}
    [DecidableEq ι] [DecidableEq J] {I : Finset ι} {S : ι → Finset J}
    (hS : (I : Set ι).PairwiseDisjoint S) (hI : I.Nonempty)
    (P : Finpartition (I.biUnion S)) (hP : IsIrreduciblePartition I S P) :
    groupComponentPartition S P = ⊤ := by
  by_contra hne
  obtain ⟨A, hA, hAI⟩ := exists_proper_part_of_ne_top (groupComponentPartition S P) hI hne
  apply hP A ((groupComponentPartition S P).le hA)
    ((groupComponentPartition S P).nonempty_of_mem_parts hA) hAI
  refine ⟨P.parts.filter (fun B => B ⊆ A.biUnion S), Finset.filter_subset _ _, ?_⟩
  exact union_groups_eq_union_blocks hS P (respectsGroups_groupComponentPartition hS P) hA

end WaveTurbulence.CumulantProducts

namespace WaveTurbulence.CumulantProducts
open scoped Classical

/-- The coarse partition into a nonempty proper subfamily and its complement. -/
@[expose] noncomputable def cutPartition {ι : Type*} [DecidableEq ι]
    (I A : Finset ι) (hA : A ⊆ I) (hne : A.Nonempty) (hAI : A ≠ I) : Finpartition I :=
  CumulantPartitions.adjoinComplementBlock I A hA hne
    (Finpartition.indiscrete (Finset.nonempty_iff_ne_empty.mp
      (Finset.sdiff_nonempty.mpr (fun hIA => hAI (Finset.Subset.antisymm hA hIA)))))

/-- The two blocks of a subfamily cut. -/
theorem cutPartition_parts {ι : Type*} [DecidableEq ι] (I A : Finset ι)
    (hA : A ⊆ I) (hne : A.Nonempty) (hAI : A ≠ I) :
    (cutPartition I A hA hne hAI).parts = {A, I \ A} := rfl

/-- A nonempty proper cut is not the one-block partition. -/
theorem cutPartition_ne_top {ι : Type*} [DecidableEq ι] (I A : Finset ι)
    (hA : A ⊆ I) (hne : A.Nonempty) (hAI : A ≠ I) : cutPartition I A hA hne hAI ≠ ⊤ := by
  intro h
  have hm : A ∈ (cutPartition I A hA hne hAI).parts := by rw [cutPartition_parts]; simp
  rw [h] at hm
  exact hAI (Finset.mem_singleton.mp (Finpartition.parts_top_subset I hm))

/-- A subfamily that is a union of fine blocks determines a respecting coarse cut. -/
theorem respectsGroups_cut_of_blockUnion {ι J : Type*} [DecidableEq ι] [DecidableEq J]
    {I : Finset ι} {S : ι → Finset J} (hS : (I : Set ι).PairwiseDisjoint S)
    (P : Finpartition (I.biUnion S)) (A : Finset ι) (hA : A ⊆ I)
    (hne : A.Nonempty) (hAI : A ≠ I) (T : Finset (Finset J))
    (hT : T ⊆ P.parts) (hU : A.biUnion S = T.biUnion id) :
    RespectsGroups S P (cutPartition I A hA hne hAI) := by
  intro B hB
  by_cases hBT : B ∈ T
  · refine ⟨A, ?_, ?_⟩
    · rw [cutPartition_parts]; simp
    · intro j hj
      rw [hU]
      exact Finset.mem_biUnion.mpr ⟨B, hBT, hj⟩
  · refine ⟨I \ A, ?_, ?_⟩
    · rw [cutPartition_parts]; simp
    · rw [biUnion_groups_sdiff hS hA]
      intro j hj
      refine Finset.mem_sdiff.mpr ⟨P.le hB hj, ?_⟩
      intro hjA
      rw [hU] at hjA
      obtain ⟨C, hC, hjC⟩ := Finset.mem_biUnion.mp hjA
      have hBC : B ≠ C := fun he => hBT (he.symm ▸ hC)
      exact Finset.disjoint_left.mp (P.disjoint hB (hT hC) hBC) hj hjC

/-- If the group components have one block, no nontrivial subfamily is a union of fine blocks. -/
theorem irreducible_of_groupComponentPartition_eq_top {ι J : Type*}
    [DecidableEq ι] [DecidableEq J] {I : Finset ι} {S : ι → Finset J}
    (hS : (I : Set ι).PairwiseDisjoint S) (P : Finpartition (I.biUnion S))
    (hP : groupComponentPartition S P = ⊤) : IsIrreduciblePartition I S P := by
  intro A hA hne hAI h
  obtain ⟨T, hT, hU⟩ := h
  have hQ := respectsGroups_cut_of_blockUnion hS P A hA hne hAI T hT hU
  have hle := groupComponentPartition_le P hQ
  rw [hP] at hle
  exact cutPartition_ne_top I A hA hne hAI (top_le_iff.mp hle)

/-- The source irreducibility condition is equivalent to connectedness of the group components. -/
theorem irreducible_iff_groupComponentPartition_eq_top {ι J : Type*}
    [DecidableEq ι] [DecidableEq J] {I : Finset ι} {S : ι → Finset J}
    (hS : (I : Set ι).PairwiseDisjoint S) (hI : I.Nonempty)
    (P : Finpartition (I.biUnion S)) :
    IsIrreduciblePartition I S P ↔ groupComponentPartition S P = ⊤ :=
  ⟨groupComponentPartition_eq_top_of_irreducible hS hI P,
    irreducible_of_groupComponentPartition_eq_top hS P⟩

end WaveTurbulence.CumulantProducts
