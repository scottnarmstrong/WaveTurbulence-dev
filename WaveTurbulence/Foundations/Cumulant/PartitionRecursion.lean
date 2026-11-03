/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Basic.Complex.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Reindexing partitions by a selected block

Finite combinatorial infrastructure for the cumulant inversion in TARGET `eqncm2`.
Avoiding a block removes it from the partition; adjoining it to a partition of
its complement reverses this operation.
-/

public section

open scoped Classical
namespace WaveTurbulence.CumulantPartitions
lemma parts_avoid_block {ι : Type*} [DecidableEq ι] {s B : Finset ι}
    (P : Finpartition s) (hB : B ∈ P.parts) :
    (P.avoid B).parts = P.parts.erase B := by
  ext A
  rw [Finpartition.mem_avoid, Finset.mem_erase]
  constructor
  · rintro ⟨C, hC, hnot, hCA⟩
    have hCB : C ≠ B := fun h => hnot (h ▸ le_rfl)
    have hdis := P.disjoint hC hB hCB
    change Disjoint C B at hdis
    have he := Finset.sdiff_eq_self_of_disjoint hdis
    rw [he] at hCA
    subst A
    exact ⟨hCB, hC⟩
  · rintro ⟨hAB, hA⟩
    have hdis := P.disjoint hA hB hAB
    change Disjoint A B at hdis
    refine ⟨A, hA, ?_, Finset.sdiff_eq_self_of_disjoint hdis⟩
    intro hsub
    exact P.ne_empty hA (hdis.eq_bot_of_le hsub)


/-- Add a nonempty block to a partition of its complement. -/
@[expose] noncomputable def adjoinComplementBlock {ι : Type*} [DecidableEq ι] (s B : Finset ι)
    (hB : B ⊆ s) (hBne : B.Nonempty) (Q : Finpartition (s \ B)) : Finpartition s :=
  Q.extend (Finset.nonempty_iff_ne_empty.mp hBne)
    (Finset.disjoint_left.mpr (fun _ hj hjB => (Finset.mem_sdiff.mp hj).2 hjB))
    (Finset.sdiff_union_of_subset hB)

lemma parts_adjoinComplementBlock {ι : Type*} [DecidableEq ι] (s B : Finset ι)
    (hB : B ⊆ s) (hBne : B.Nonempty) (Q : Finpartition (s \ B)) :
    (adjoinComplementBlock s B hB hBne Q).parts = insert B Q.parts := rfl

lemma avoid_adjoinComplementBlock {ι : Type*} [DecidableEq ι] (s B : Finset ι)
    (hB : B ⊆ s) (hBne : B.Nonempty) (Q : Finpartition (s \ B)) :
    (adjoinComplementBlock s B hB hBne Q).avoid B = Q := by
  apply Finpartition.ext
  ext A
  rw [Finpartition.mem_avoid]
  simp only [parts_adjoinComplementBlock, Finset.mem_insert]
  constructor
  · rintro ⟨C, hC, hnot, hCA⟩
    rcases hC with rfl | hC
    · exact (hnot le_rfl).elim
    · have hdis : Disjoint C B := Finset.disjoint_left.mpr fun _ hj hjB =>
        (Finset.mem_sdiff.mp (Q.le hC hj)).2 hjB
      rw [Finset.sdiff_eq_self_of_disjoint hdis] at hCA
      exact hCA ▸ hC
  · intro hA
    have hdis : Disjoint A B := Finset.disjoint_left.mpr fun _ hj hjB =>
      (Finset.mem_sdiff.mp (Q.le hA hj)).2 hjB
    refine ⟨A, Or.inr hA, ?_, Finset.sdiff_eq_self_of_disjoint hdis⟩
    intro hsub
    exact Q.ne_empty hA (hdis.eq_bot_of_le hsub)

lemma adjoinComplementBlock_avoid {ι : Type*} [DecidableEq ι] {s B : Finset ι}
    (P : Finpartition s) (hB : B ∈ P.parts) :
    adjoinComplementBlock s B (P.le hB) (P.nonempty_of_mem_parts hB) (P.avoid B) = P := by
  apply Finpartition.ext
  rw [parts_adjoinComplementBlock, parts_avoid_block P hB, Finset.insert_erase hB]

abbrev SelectedBlock {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : Finset ι → Prop) :=
  {B : s.powerset // B.1.Nonempty ∧ p B.1}
abbrev MarkedPartition {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : Finset ι → Prop) :=
  Σ P : Finpartition s, {B : P.parts // p B.1}

lemma markedPartition_ext {ι : Type*} [DecidableEq ι] {s : Finset ι} {p : Finset ι → Prop}
    (x y : MarkedPartition s p) (hP : x.1 = y.1) (hB : x.2.1.1 = y.2.1.1) : x = y := by
  rcases x with ⟨P, ⟨⟨B, hBP⟩, hnotB⟩⟩
  rcases y with ⟨Q, ⟨⟨C, hCQ⟩, hnotC⟩⟩
  dsimp only at hP hB
  cases hP
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  exact Subtype.ext (Subtype.ext hB)

/-- Marking one block is equivalent to partitioning the complement of a selected block. -/
@[expose] noncomputable def blockPartitionEquiv {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : Finset ι → Prop) :
    (Σ B : SelectedBlock s p, Finpartition (s \ B.1.1)) ≃ MarkedPartition s p where
  toFun x := ⟨adjoinComplementBlock s x.1.1.1 (Finset.mem_powerset.mp x.1.1.property)
      x.1.property.1 x.2,
    ⟨⟨x.1.1.1, Finset.mem_insert_self _ _⟩, x.1.property.2⟩⟩
  invFun x := ⟨⟨⟨x.2.1.1, Finset.mem_powerset.mpr (x.1.le x.2.1.property)⟩,
    x.1.nonempty_of_mem_parts x.2.1.property, x.2.property⟩, x.1.avoid x.2.1.1⟩
  left_inv := by
    rintro ⟨⟨⟨B, hBs⟩, hBne, hnot⟩, Q⟩
    dsimp only
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    exact avoid_adjoinComplementBlock s B (Finset.mem_powerset.mp hBs) hBne Q
  right_inv := by
    rintro ⟨P, ⟨⟨B, hB⟩, hnot⟩⟩
    apply markedPartition_ext
    · exact adjoinComplementBlock_avoid P hB
    · rfl

lemma sum_selected_complement_partitions {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : Finset ι → Prop) [DecidablePred p] (F : (B : Finset ι) → Finpartition (s \ B) → ℂ) :
    (∑ B : SelectedBlock s p, ∑ Q : Finpartition (s \ B.1.1), F B.1.1 Q) =
      ∑ P : Finpartition s, ∑ B : {B : P.parts // p B.1}, F B.1.1 (P.avoid B.1.1) := by
  have h := Fintype.sum_equiv (blockPartitionEquiv s p)
    (fun x : (Σ B : SelectedBlock s p, Finpartition (s \ B.1.1)) => F x.1.1.1 x.2)
    (fun x : MarkedPartition s p => F x.2.1.1 (x.1.avoid x.2.1.1))
    (by
      rintro ⟨B, Q⟩
      exact congrArg (F B.1.1) (avoid_adjoinComplementBlock s B.1.1
        (Finset.mem_powerset.mp B.1.property) B.property.1 Q).symm)
  simpa only [Fintype.sum_sigma] using h
end WaveTurbulence.CumulantPartitions

namespace WaveTurbulence.CumulantPartitions
open scoped Classical

/-- All blocks except the block of `i`, represented by the condition that they avoid `i`. -/
@[expose] noncomputable def excludedPartEquiv {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (P : Finpartition s) (i : ι) (hi : i ∈ s) :
    {B : P.parts // i ∉ B.1} ≃ {B // B ∈ P.parts.erase (P.part i)} where
  toFun B := ⟨B.1.1, Finset.mem_erase.mpr
    ⟨fun h => B.property (h.symm ▸ P.mem_part hi), B.1.property⟩⟩
  invFun B := ⟨⟨B.1, (Finset.mem_erase.mp B.property).2⟩,
    fun h => (Finset.mem_erase.mp B.property).1
      (P.part_eq_of_mem (Finset.mem_erase.mp B.property).2 h).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exactly one block contains a fixed element of the partitioned set. -/
theorem card_excluded_parts {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (P : Finpartition s) (i : ι) (hi : i ∈ s) :
    Nat.card {B : P.parts // i ∉ B.1} = P.parts.card - 1 := by
  rw [Nat.card_congr (excludedPartEquiv P i hi), Nat.card_eq_fintype_card,
    Fintype.card_coe, Finset.card_erase_of_mem (P.part_mem.mpr hi)]

/-- A partition of a nonempty set with one block is the indiscrete partition. -/
theorem eq_indiscrete_of_card_parts_eq_one {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (P : Finpartition s) (hs : s.Nonempty) (hP : P.parts.card = 1) :
    P = Finpartition.indiscrete (Finset.nonempty_iff_ne_empty.mp hs) := by
  obtain ⟨A, hA⟩ := Finset.card_eq_one.mp hP
  have he : A = s := by
    have h := P.sup_parts
    rw [hA, Finset.sup_singleton, id_eq] at h
    exact h
  subst A
  exact Finpartition.ext hA

end WaveTurbulence.CumulantPartitions

namespace WaveTurbulence.CumulantPartitions
open scoped Classical

/-- Subsets of `s` avoiding a distinguished index, including the empty subset. -/
abbrev AvoidingSubset {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι) :=
  {B : s.powerset // i ∉ B.1}

/-- Complementation exchanges a block containing `i` and a subset avoiding `i`. -/
@[expose] noncomputable def complementBlockEquiv {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i : ι) (hi : i ∈ s) :
    SelectedBlock s (fun A => i ∈ A) ≃ AvoidingSubset s i where
  toFun A := ⟨⟨s \ A.1.1, Finset.mem_powerset.mpr Finset.sdiff_subset⟩,
    fun h => (Finset.mem_sdiff.mp h).2 A.property.2⟩
  invFun B := ⟨⟨s \ B.1.1, Finset.mem_powerset.mpr Finset.sdiff_subset⟩,
    ⟨i, Finset.mem_sdiff.mpr ⟨hi, B.property⟩⟩, Finset.mem_sdiff.mpr ⟨hi, B.property⟩⟩
  left_inv A := Subtype.ext (Subtype.ext
    (Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp A.1.property)))
  right_inv B := Subtype.ext (Subtype.ext
    (Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp B.1.property)))

/-- Split off the empty avoiding subset. -/
@[expose] noncomputable def avoidingSubsetEquivOption {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i : ι) :
    AvoidingSubset s i ≃ Option (SelectedBlock s (fun B => i ∉ B)) where
  toFun B := if h : B.1.1 = ∅ then none else
    some ⟨B.1, Finset.nonempty_iff_ne_empty.mpr h, B.property⟩
  invFun
    | none => ⟨⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset s)⟩, Finset.notMem_empty i⟩
    | some B => ⟨B.1, B.property.2⟩
  left_inv B := by
    by_cases h : B.1.1 = ∅
    · simp only [h, ↓reduceDIte]
      exact Subtype.ext (Subtype.ext h.symm)
    · simp only [h, ↓reduceDIte]
  right_inv B := by
    cases B with
    | none => simp only [↓reduceDIte]
    | some B => simp only [Finset.nonempty_iff_ne_empty.mp B.property.1, ↓reduceDIte]

/-- A sum over avoiding subsets splits into the empty term and the nonempty subsets. -/
theorem sum_avoidingSubset {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι)
    (F : Finset ι → ℂ) :
    (∑ B : AvoidingSubset s i, F B.1.1) = F ∅ +
      ∑ B : SelectedBlock s (fun B => i ∉ B), F B.1.1 := by
  have h := Fintype.sum_equiv (avoidingSubsetEquivOption s i)
    (fun B : AvoidingSubset s i => F B.1.1)
    (fun B : Option (SelectedBlock s (fun B => i ∉ B)) =>
      match B with | none => F ∅ | some B => F B.1.1)
    (by
      intro B
      dsimp [avoidingSubsetEquivOption]
      split_ifs with h
      · rw [h]
      · rfl)
  simpa only [Fintype.sum_option] using h

end WaveTurbulence.CumulantPartitions
