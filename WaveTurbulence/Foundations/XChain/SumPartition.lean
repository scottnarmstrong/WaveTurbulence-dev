/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Fintype.Sum
/-! Disjoint carrier sums of finite partitions, with the original blocks preserved. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

noncomputable def sumPartition {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition (univ : Finset α)) (Q : Finpartition (univ : Finset β)) :
    Finpartition (univ : Finset (α ⊕ β)) :=
  Finpartition.ofSetoid (Setoid.ker (Sum.map P.part Q.part))

theorem sumPartition_mem_part_inl {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition (univ : Finset α)) (Q : Finpartition (univ : Finset β)) (a b : α) :
    Sum.inl b ∈ (sumPartition P Q).part (.inl a) ↔ b ∈ P.part a := by
  rw [sumPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  change (Sum.inl (P.part a) = Sum.inl (P.part b)) ↔ _
  rw [Sum.inl.injEq]
  exact eq_comm.trans (P.mem_part_iff_part_eq_part (mem_univ b) (mem_univ a)).symm

theorem sumPartition_mem_part_inr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition (univ : Finset α)) (Q : Finpartition (univ : Finset β)) (a b : β) :
    Sum.inr b ∈ (sumPartition P Q).part (.inr a) ↔ b ∈ Q.part a := by
  rw [sumPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  change (Sum.inr (Q.part a) = Sum.inr (Q.part b)) ↔ _
  rw [Sum.inr.injEq]
  exact eq_comm.trans (Q.mem_part_iff_part_eq_part (mem_univ b) (mem_univ a)).symm

theorem sumPartition_not_mem_part_inl {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition (univ : Finset α)) (Q : Finpartition (univ : Finset β)) (a : α) (b : β) :
    Sum.inr b ∉ (sumPartition P Q).part (.inl a) := by
  rw [sumPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  exact Sum.inl_ne_inr

theorem sumPartition_not_mem_part_inr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition (univ : Finset α)) (Q : Finpartition (univ : Finset β)) (a : β) (b : α) :
    Sum.inl b ∉ (sumPartition P Q).part (.inr a) := by
  rw [sumPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  exact Sum.inr_ne_inl

theorem sumPartition_part_inl {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition (univ : Finset α)) (Q : Finpartition (univ : Finset β)) (a : α) :
    (sumPartition P Q).part (.inl a) = (P.part a).map Function.Embedding.inl := by
  ext z
  cases z with
  | inl b =>
    rw [sumPartition_mem_part_inl]
    simp only [Finset.mem_map, Function.Embedding.inl_apply, Sum.inl.injEq, exists_eq_right]
  | inr b =>
    have h := sumPartition_not_mem_part_inl P Q a b
    simp only [h, Finset.mem_map, Function.Embedding.inl_apply, Sum.inl_ne_inr, and_false, exists_false]

theorem sumPartition_part_inr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (P : Finpartition (univ : Finset α)) (Q : Finpartition (univ : Finset β)) (a : β) :
    (sumPartition P Q).part (.inr a) = (Q.part a).map Function.Embedding.inr := by
  ext z
  cases z with
  | inl b =>
    have h := sumPartition_not_mem_part_inr P Q a b
    simp only [h, Finset.mem_map, Function.Embedding.inr_apply, Sum.inr_ne_inl, and_false, exists_false]
  | inr b =>
    rw [sumPartition_mem_part_inr]
    simp only [Finset.mem_map, Function.Embedding.inr_apply, Sum.inr.injEq, exists_eq_right]

end WaveTurbulence.Induct
