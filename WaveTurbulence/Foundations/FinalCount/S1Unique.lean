/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.S1Basic
import Mathlib.Tactic

/-!
# Stage 1 combinatorics: uniqueness in TARGET vinechainlem (L1930-L1933)

Any collection of disjoint HV/VC/HVC/DV groups covering every designated vine-like object is the
collection of maximal HV/VC/HVC/DV atom sets.  Uniqueness is therefore formal and independent of
the overlap classification.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The maximal HV/VC/HVC/DV atom sets of a molecule. -/
@[expose] def maximalGroups (M : Molecule V D) : Set (Finset V) :=
  {S | IsStage1Group M S ∧ ∀ T, IsStage1Group M T → S ⊆ T → T = S}

theorem eq_of_mem_inter {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartition M C) {S S' : Finset V} (hS : S ∈ C) (hS' : S' ∈ C) {z : V}
    (hz : z ∈ S) (hz' : z ∈ S') : S = S' := by
  by_contra hne
  exact Finset.disjoint_left.mp (hC.2.1 hS hS' hne) hz hz'

theorem cover_of_vineLike {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartition M C) {T : Finset V} (hT : IsVineLikeSet M T) :
    ∃ S' ∈ C, T ⊆ S' := by
  obtain ⟨P, rfl⟩ := object_of_isVineLikeSet hT
  exact hC.2.2 P

theorem mem_collection_isStage1Group {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartition M C) {S : Finset V} (hS : S ∈ C) : IsStage1Group M S := by
  obtain ⟨a, b, h⟩ := hC.1 S hS
  exact ⟨a, b, h⟩

theorem partition_subset_maximal {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartition M C) : C ⊆ maximalGroups M := by
  intro S hS
  refine ⟨mem_collection_isStage1Group hC hS, fun T hT hST => ?_⟩
  have hSne := (mem_collection_isStage1Group hC hS).nonempty
  rcases isStage1Group_iff.mp hT with hv | ⟨a, b, hdv⟩
  · obtain ⟨S', hS', hTS'⟩ := cover_of_vineLike hC hv
    obtain ⟨z, hz⟩ := hSne
    have := eq_of_mem_inter hC hS hS' hz (hTS' (hST hz))
    subst this
    exact Finset.Subset.antisymm hTS' hST
  · obtain ⟨A, B, hA, hB, hAB, rfl⟩ := hdv
    obtain ⟨SA, hSA, hASA⟩ := cover_of_vineLike hC (isVineLikeSet_of_isVine hA)
    obtain ⟨SB, hSB, hBSB⟩ := cover_of_vineLike hC (isVineLikeSet_of_isVine hB)
    have haA : a ∈ A := hA.1.2.1
    have haB : a ∈ B := hB.1.2.1
    have hSAB : SA = SB := eq_of_mem_inter hC hSA hSB (hASA haA) (hBSB haB)
    subst hSAB
    obtain ⟨z, hz⟩ := hSne
    rcases mem_union.mp (hST hz) with hzA | hzB
    · have hSe : S = SA := eq_of_mem_inter hC hS hSA hz (hASA hzA)
      subst hSe
      exact Finset.Subset.antisymm (union_subset hASA hBSB) hST
    · have hSe : S = SA := eq_of_mem_inter hC hS hSA hz (hBSB hzB)
      subst hSe
      exact Finset.Subset.antisymm (union_subset hASA hBSB) hST

theorem maximal_subset_partition {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartition M C) : maximalGroups M ⊆ C := by
  rintro T ⟨hT, hmax⟩
  rcases isStage1Group_iff.mp hT with hv | ⟨a, b, hdv⟩
  · obtain ⟨S', hS', hTS'⟩ := cover_of_vineLike hC hv
    have := hmax S' (mem_collection_isStage1Group hC hS') hTS'
    rwa [this] at hS'
  · obtain ⟨A, B, hA, hB, hAB, rfl⟩ := hdv
    obtain ⟨SA, hSA, hASA⟩ := cover_of_vineLike hC (isVineLikeSet_of_isVine hA)
    obtain ⟨SB, hSB, hBSB⟩ := cover_of_vineLike hC (isVineLikeSet_of_isVine hB)
    have hSAB : SA = SB := eq_of_mem_inter hC hSA hSB (hASA hA.1.2.1) (hBSB hB.1.2.1)
    subst hSAB
    have := hmax SA (mem_collection_isStage1Group hC hSA) (union_subset hASA hBSB)
    rwa [this] at hSA

/-- Uniqueness half of TARGET vinechainlem: a valid collection is the set of maximal groups. -/
theorem partition_eq_maximalGroups {M : Molecule V D} {C : Set (Finset V)}
    (hC : IsSourceVinePartition M C) : C = maximalGroups M :=
  Set.Subset.antisymm (partition_subset_maximal hC) (maximal_subset_partition hC)

/-- Uniqueness half of TARGET vinechainlem (L1930-L1933). -/
theorem partition_unique {M : Molecule V D} {C C' : Set (Finset V)}
    (hC : IsSourceVinePartition M C) (hC' : IsSourceVinePartition M C') : C = C' :=
  (partition_eq_maximalGroups hC).trans (partition_eq_maximalGroups hC').symm

end WaveTurbulence.Stage1
