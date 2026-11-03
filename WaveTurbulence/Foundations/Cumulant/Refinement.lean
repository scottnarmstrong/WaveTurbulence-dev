/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cumulant.Coarsening

/-!
# Independent refinements of partition blocks

A refinement of `G` is the same as a partition of each block of `G`. This is the
finite product-of-sums reindexing in TARGET Lemma `propertycm`.
-/

public section

namespace WaveTurbulence.CumulantProducts
open scoped Classical

/-- Restricting a refinement to a coarse block keeps exactly the fine blocks it contains. -/
theorem parts_restrict_of_le {ι : Type*} [DecidableEq ι] {I A : Finset ι}
    (R G : Finpartition I) (hRG : R ≤ G) (hA : A ∈ G.parts) :
    (R.restrict (G.le hA)).parts = R.parts.filter (fun B => B ⊆ A) := by
  ext C
  rw [Finpartition.parts_restrict, Finset.mem_erase, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨hC, B, hB, rfl⟩
    obtain ⟨D, hD, hBD⟩ := hRG hB
    have hDA : D = A := eq_parts_of_nonempty_subset G
      (Finset.nonempty_iff_ne_empty.mpr hC) hD hA
      (Finset.inter_subset_left.trans hBD) Finset.inter_subset_right
    subst D
    change B ∩ A ∈ R.parts ∧ B ∩ A ⊆ A
    rw [Finset.inter_eq_left.mpr hBD]
    exact ⟨hB, hBD⟩
  · rintro ⟨hC, hCA⟩
    exact ⟨R.ne_empty hC, C, hC, Finset.inter_eq_left.mpr hCA⟩

/-- Join independently chosen partitions of the coarse blocks. -/
@[expose] noncomputable def bindPartition {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (G : Finpartition I) (F : (A : G.parts) → Finpartition A.1) : Finpartition I :=
  G.bind (fun A hA => F ⟨A, hA⟩)

/-- Fine-block membership in a bound partition. -/
theorem mem_bindPartition {ι : Type*} [DecidableEq ι] {I B : Finset ι}
    (G : Finpartition I) (F : (A : G.parts) → Finpartition A.1) :
    B ∈ (bindPartition G F).parts ↔ ∃ A : G.parts, B ∈ (F A).parts := by
  rw [bindPartition, Finpartition.mem_bind]
  constructor
  · rintro ⟨A, hA, hB⟩
    exact ⟨⟨A, hA⟩, hB⟩
  · rintro ⟨A, hB⟩
    exact ⟨A.1, A.property, hB⟩

/-- The bound partition refines the original coarse partition. -/
theorem bindPartition_le {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (G : Finpartition I) (F : (A : G.parts) → Finpartition A.1) : bindPartition G F ≤ G := by
  intro B hB
  obtain ⟨A, hBA⟩ := (mem_bindPartition G F).mp hB
  exact ⟨A.1, A.property, (F A).le hBA⟩

/-- Binding the restrictions of a refinement recovers that refinement. -/
theorem bindPartition_restrict {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (R G : Finpartition I) (hRG : R ≤ G) :
    bindPartition G (fun A : G.parts => R.restrict (G.le A.property)) = R := by
  apply Finpartition.ext
  ext B
  rw [mem_bindPartition]
  constructor
  · rintro ⟨A, hB⟩
    rw [parts_restrict_of_le R G hRG A.property, Finset.mem_filter] at hB
    exact hB.1
  · intro hB
    obtain ⟨A, hA, hBA⟩ := hRG hB
    refine ⟨⟨A, hA⟩, ?_⟩
    rw [parts_restrict_of_le R G hRG hA, Finset.mem_filter]
    exact ⟨hB, hBA⟩

/-- Restriction to a coarse block recovers its chosen subpartition. -/
theorem restrict_bindPartition {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (G : Finpartition I) (F : (A : G.parts) → Finpartition A.1) (A : G.parts) :
    (bindPartition G F).restrict (G.le A.property) = F A := by
  apply Finpartition.ext
  rw [parts_restrict_of_le _ G (bindPartition_le G F) A.property]
  ext B
  rw [Finset.mem_filter, mem_bindPartition]
  constructor
  · rintro ⟨⟨C, hBC⟩, hBA⟩
    have hCA : C.1 = A.1 := eq_parts_of_nonempty_subset G
      ((F C).nonempty_of_mem_parts hBC) C.property A.property ((F C).le hBC) hBA
    have he : C = A := Subtype.ext hCA
    subst C
    exact hBC
  · intro hB
    exact ⟨⟨A, hB⟩, (F A).le hB⟩

/-- A refinement is the same as a family of partitions of the coarse blocks. -/
@[expose] noncomputable def refinementEquiv {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (G : Finpartition I) :
    ((A : G.parts) → Finpartition A.1) ≃ {R : Finpartition I // R ≤ G} where
  toFun F := ⟨bindPartition G F, bindPartition_le G F⟩
  invFun R A := R.1.restrict (G.le A.property)
  left_inv F := funext (restrict_bindPartition G F)
  right_inv R := Subtype.ext (bindPartition_restrict R.1 G R.2)

/-- Blocks arising from distinct coarse blocks are disjoint as a family of fine blocks. -/
theorem disjoint_parts_of_distinct_blocks {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (G : Finpartition I) (F : (A : G.parts) → Finpartition A.1)
    (A C : G.parts) (hAC : A ≠ C) : Disjoint (F A).parts (F C).parts := by
  apply Finset.disjoint_left.mpr
  intro B hBA hBC
  have hd := (G.disjoint A.property C.property (fun h => hAC (Subtype.ext h))).mono
    ((F A).le hBA) ((F C).le hBC)
  exact (F A).ne_empty hBA (disjoint_self.mp hd)

/-- A product over a bound partition is the product over the independently refined blocks. -/
theorem prod_bindPartition {ι M : Type*} [DecidableEq ι] [CommMonoid M] {I : Finset ι}
    (G : Finpartition I) (F : (A : G.parts) → Finpartition A.1) (L : Finset ι → M) :
    (∏ B ∈ (bindPartition G F).parts, L B) = ∏ A : G.parts, ∏ B ∈ (F A).parts, L B := by
  change (∏ B ∈ G.parts.attach.biUnion (fun A : G.parts => (F A).parts), L B) = _
  rw [Finset.prod_biUnion (fun A _ C _ hAC => disjoint_parts_of_distinct_blocks G F A C hAC)]
  rfl

/-- Products of exponential partition sums expand over the refinements of the coarse partition. -/
theorem prod_partitionExp_eq_sum_refinements {ι : Type*} [DecidableEq ι] {I : Finset ι}
    (G : Finpartition I) (L : Finset ι → ℂ) :
    (∏ A ∈ G.parts, CumulantPartitions.partitionExp L A) =
      ∑ R : {R : Finpartition I // R ≤ G}, ∏ B ∈ R.1.parts, L B := by
  rw [← Finset.prod_coe_sort]
  simp only [CumulantPartitions.partitionExp]
  rw [Fintype.prod_sum]
  have h := Fintype.sum_equiv (refinementEquiv G)
    (fun F : (A : G.parts) → Finpartition A.1 => ∏ A : G.parts, ∏ B ∈ (F A).parts, L B)
    (fun R : {R : Finpartition I // R ≤ G} => ∏ B ∈ R.1.parts, L B)
    (fun F => (prod_bindPartition G F L).symm)
  exact h

end WaveTurbulence.CumulantProducts
