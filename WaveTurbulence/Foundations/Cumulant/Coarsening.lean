/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cumulant.PartitionLift

/-!
# Partitions of the blocks of a partition

Coarsenings of `R` are the partitions of its set of blocks. This identifies the
Möbius coefficient sum needed in TARGET Lemma `propertycm`.
-/

public section

namespace WaveTurbulence.CumulantProducts
open scoped Classical

/-- Distinct partition blocks cannot both contain the same nonempty set. -/
theorem eq_parts_of_nonempty_subset {ι : Type*} [DecidableEq ι] {I A C D : Finset ι}
    (Q : Finpartition I) (hA : A.Nonempty) (hC : C ∈ Q.parts) (hD : D ∈ Q.parts)
    (hAC : A ⊆ C) (hAD : A ⊆ D) : C = D := by
  by_contra hne
  obtain ⟨j, hj⟩ := hA
  exact Finset.disjoint_left.mp (Q.disjoint hC hD hne) (hAC hj) (hAD hj)

/-- A block of a coarsening is the union of the fine blocks it contains. -/
theorem biUnion_parts_below_eq {ι : Type*} [DecidableEq ι] {I C : Finset ι}
    (R Q : Finpartition I) (hRQ : R ≤ Q) (hC : C ∈ Q.parts) :
    (R.parts.filter (fun A => A ⊆ C)).biUnion id = C := by
  ext j
  constructor
  · intro h
    obtain ⟨A, hA, hjA⟩ := Finset.mem_biUnion.mp h
    exact (Finset.mem_filter.mp hA).2 hjA
  · intro hj
    have hjI := Q.le hC hj
    obtain ⟨D, hD, hRD⟩ := hRQ (R.part_mem.mpr hjI)
    have hDC : D = C := eq_parts_of_nonempty_subset Q ⟨j, Finset.mem_singleton_self j⟩
      hD hC (by simpa using hRD (R.mem_part hjI)) (by simpa using hj)
    subst D
    exact Finset.mem_biUnion.mpr ⟨R.part j,
      Finset.mem_filter.mpr ⟨R.part_mem.mpr hjI, hRD⟩, R.mem_part hjI⟩

/-- Fine blocks contained in a fixed coarse block, indexed by the type of fine blocks. -/
@[expose] noncomputable def blocksBelow {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R : Finpartition I) (C : Finset ι) : Finset R.parts :=
  Finset.univ.filter (fun A : R.parts => A.1 ⊆ C)

/-- The union of the fine blocks below a coarse block recovers that block. -/
theorem biUnion_blocksBelow {ι : Type*} [DecidableEq ι] {I C : Finset ι}
    (R Q : Finpartition I) (hRQ : R ≤ Q) (hC : C ∈ Q.parts) :
    (blocksBelow R C).biUnion (fun A : R.parts => A.1) = C := by
  conv_rhs => rw [← biUnion_parts_below_eq R Q hRQ hC]
  ext j
  simp only [blocksBelow, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨A, hAC, hj⟩
    exact ⟨A.1, ⟨A.property, hAC⟩, hj⟩
  · rintro ⟨A, ⟨hA, hAC⟩, hj⟩
    exact ⟨⟨A, hA⟩, hAC, hj⟩

/-- A coarsening induces a partition of the type of fine blocks. -/
@[expose] noncomputable def coarseningOnParts {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R Q : Finpartition I) (hRQ : R ≤ Q) : Finpartition (Finset.univ : Finset R.parts) :=
  Finpartition.ofExistsUnique (Q.parts.image (blocksBelow R))
    (by intro A _; exact Finset.subset_univ A)
    (by
      intro A _
      obtain ⟨C, hC, hAC⟩ := hRQ A.property
      refine ⟨blocksBelow R C,
        ⟨Finset.mem_image.mpr ⟨C, hC, rfl⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ A, hAC⟩⟩, ?_⟩
      intro B hB
      obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hB.1
      have hAD : A.1 ⊆ D := (Finset.mem_filter.mp hB.2).2
      have he : D = C := eq_parts_of_nonempty_subset Q (R.nonempty_of_mem_parts A.property)
        hD hC hAD hAC
      rw [he])
    (by
      intro h
      obtain ⟨C, hC, he⟩ := Finset.mem_image.mp h
      have hU := biUnion_blocksBelow R Q hRQ hC
      rw [he, Finset.biUnion_empty] at hU
      exact Q.ne_empty hC hU.symm)

end WaveTurbulence.CumulantProducts

namespace WaveTurbulence.CumulantProducts
open scoped Classical

/-- The blocks of a partition form a disjoint family. -/
theorem parts_pairwiseDisjoint {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R : Finpartition I) : ((Finset.univ : Finset R.parts) : Set R.parts).PairwiseDisjoint (fun A => A.1) := by
  intro A _ B _ hAB
  exact R.disjoint A.property B.property (fun h => hAB (Subtype.ext h))

/-- Every partition block is nonempty. -/
theorem parts_nonempty {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R : Finpartition I) : ∀ A ∈ (Finset.univ : Finset R.parts), A.1.Nonempty :=
  fun A _ => R.nonempty_of_mem_parts A.property

/-- The union of the type-indexed blocks of a partition is the original finite set. -/
theorem biUnion_type_parts {ι : Type*} [DecidableEq ι] {I : Finset ι} (R : Finpartition I) :
    (Finset.univ : Finset R.parts).biUnion (fun A => A.1) = I := by
  ext j
  constructor
  · intro hj
    obtain ⟨A, _, hjA⟩ := Finset.mem_biUnion.mp hj
    exact R.le A.property hjA
  · intro hj
    exact Finset.mem_biUnion.mpr ⟨⟨R.part j, R.part_mem.mpr hj⟩, Finset.mem_univ _, R.mem_part hj⟩

/-- Replace each block of blocks by the union of its fine blocks. -/
@[expose] noncomputable def coarseningLift {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R : Finpartition I) (K : Finpartition (Finset.univ : Finset R.parts)) : Finpartition I :=
  (groupPartition Finset.univ (fun A : R.parts => A.1)
    (parts_pairwiseDisjoint R) (parts_nonempty R) K).copy (biUnion_type_parts R)

/-- Lifting a partition of blocks gives a coarsening of the fine partition. -/
theorem le_coarseningLift {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R : Finpartition I) (K : Finpartition (Finset.univ : Finset R.parts)) : R ≤ coarseningLift R K := by
  intro B hB
  let A : R.parts := ⟨B, hB⟩
  refine ⟨(K.part A).biUnion (fun C : R.parts => C.1), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨K.part A, K.part_mem.mpr (Finset.mem_univ A), rfl⟩
  · intro j hj
    exact Finset.mem_biUnion.mpr ⟨A, K.mem_part (Finset.mem_univ A), hj⟩

/-- Lifting partitions of blocks preserves their number of blocks. -/
theorem coarseningLift_card {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R : Finpartition I) (K : Finpartition (Finset.univ : Finset R.parts)) :
    (coarseningLift R K).parts.card = K.parts.card :=
  groupPartition_card Finset.univ (fun A : R.parts => A.1)
    (parts_pairwiseDisjoint R) (parts_nonempty R) K

/-- Different partitions of fine blocks give different coarsenings. -/
theorem coarseningLift_injective {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R : Finpartition I) : Function.Injective (coarseningLift R) := by
  intro K L h
  apply groupPartition_injective Finset.univ (fun A : R.parts => A.1)
    (parts_pairwiseDisjoint R) (parts_nonempty R)
  apply Finpartition.ext
  have hp := congrArg (fun Q : Finpartition I => Q.parts) h
  exact hp

/-- Recover a coarsening from its induced partition of fine blocks. -/
theorem coarseningLift_coarseningOnParts {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R Q : Finpartition I) (hRQ : R ≤ Q) : coarseningLift R (coarseningOnParts R Q hRQ) = Q := by
  apply Finpartition.ext
  change (Q.parts.image (blocksBelow R)).image
    (fun A : Finset R.parts => A.biUnion (fun B : R.parts => B.1)) = Q.parts
  rw [Finset.image_image]
  calc
    _ = Q.parts.image id := Finset.image_congr (fun C hC => biUnion_blocksBelow R Q hRQ hC)
    _ = Q.parts := Finset.image_id

/-- Partitions of the fine blocks are exactly the coarsenings of the fine partition. -/
@[expose] noncomputable def coarseningEquiv {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R : Finpartition I) :
    Finpartition (Finset.univ : Finset R.parts) ≃ {Q : Finpartition I // R ≤ Q} :=
  Equiv.ofBijective (fun K => ⟨coarseningLift R K, le_coarseningLift R K⟩)
    ⟨fun _K _L h => coarseningLift_injective R (congrArg Subtype.val h),
      fun Q => ⟨coarseningOnParts R Q.1 Q.2, Subtype.ext (coarseningLift_coarseningOnParts R Q.1 Q.2)⟩⟩

end WaveTurbulence.CumulantProducts
