/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Order.Partition.Finpartition
/-! Finite partitions transport through an embedding onto the exact image of their carrier. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def embeddingPartition {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) {s : Finset α} (P : Finpartition s) : Finpartition (s.map f) where
  parts := P.parts.map (Finset.mapEmbedding f).toEmbedding
  supIndep := by
    classical
    rw [supIndep_iff_pairwiseDisjoint]
    intro A hA B hB hAB
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hA
    obtain ⟨b, hb, rfl⟩ := mem_map.mp hB
    exact (Finset.disjoint_map f).mpr (P.disjoint ha hb (fun he => hAB (congrArg (fun A => A.map f) he)))
  sup_parts := by
    classical
    ext b
    rw [mem_sup]
    constructor
    · rintro ⟨A, hA, hb⟩
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hA
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hb
      exact mem_map.mpr ⟨i, P.le ha hi, rfl⟩
    · intro hb
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hb
      exact ⟨(P.part i).map f,
        mem_map.mpr ⟨P.part i, P.part_mem.mpr hi, rfl⟩,
        mem_map.mpr ⟨i, P.mem_part hi, rfl⟩⟩
  bot_notMem := by
    intro h
    obtain ⟨A, hA, he⟩ := mem_map.mp h
    have hzero : A = ∅ := Finset.map_eq_empty.mp he
    exact P.bot_notMem ((congrArg (fun A : Finset α => A ∈ P.parts) hzero).mp hA)

theorem embeddingPartition_parts {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) {s : Finset α} (P : Finpartition s) :
    (embeddingPartition f P).parts = P.parts.map (Finset.mapEmbedding f).toEmbedding := rfl

theorem embeddingPartition_part {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) {s : Finset α} (P : Finpartition s) {a : α} (ha : a ∈ s) :
    (embeddingPartition f P).part (f a) = (P.part a).map f := by
  apply (embeddingPartition f P).part_eq_of_mem
  · exact mem_map.mpr ⟨P.part a, P.part_mem.mpr ha, rfl⟩
  · exact mem_map.mpr ⟨a, P.mem_part ha, rfl⟩

theorem embeddingPartition_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (s : Finset α) : Function.Injective (embeddingPartition f (s := s)) := by
  intro P Q he
  apply Finpartition.ext
  exact Finset.map_injective (Finset.mapEmbedding f).toEmbedding (congrArg Finpartition.parts he)

end WaveTurbulence.Induct
