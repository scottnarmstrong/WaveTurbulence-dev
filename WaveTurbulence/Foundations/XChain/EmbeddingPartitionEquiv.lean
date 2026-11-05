/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.EmbeddingPartition
/-! Every partition of an embedded finite carrier comes from a unique source partition. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

noncomputable def pullbackEmbeddingPartition {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (s : Finset α) (Q : Finpartition (s.map f)) : Finpartition s :=
  Finpartition.ofSetSetoid (Setoid.ker (fun a => Q.part (f a))) s

theorem pullbackEmbeddingPartition_mem_part {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (s : Finset α) (Q : Finpartition (s.map f)) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) :
    b ∈ (pullbackEmbeddingPartition f s Q).part a ↔ f b ∈ Q.part (f a) := by
  rw [pullbackEmbeddingPartition, Finpartition.mem_part_ofSetSetoid_iff_rel]
  have hfa : f a ∈ s.map f := mem_map.mpr ⟨a, ha, rfl⟩
  have hfb : f b ∈ s.map f := mem_map.mpr ⟨b, hb, rfl⟩
  constructor
  · rintro ⟨_, _, he⟩
    exact (congrArg (fun B : Finset β => f b ∈ B) he).mpr (Q.mem_part hfb)
  · intro he
    exact ⟨ha, hb, (Q.part_eq_of_mem (Q.part_mem.mpr hfa) he).symm⟩

theorem embeddingPartition_pullback_part {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (s : Finset α) (Q : Finpartition (s.map f)) {a : α} (ha : a ∈ s) :
    (embeddingPartition f (pullbackEmbeddingPartition f s Q)).part (f a) = Q.part (f a) := by
  rw [embeddingPartition_part f _ ha]
  ext b
  constructor
  · intro hb
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hb
    exact (pullbackEmbeddingPartition_mem_part f s Q ha ((pullbackEmbeddingPartition f s Q).part_subset a hi)).mp hi
  · intro hb
    have hbt := Q.part_subset (f a) hb
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hbt
    exact mem_map.mpr ⟨i, (pullbackEmbeddingPartition_mem_part f s Q ha hi).mpr hb, rfl⟩

theorem embeddingPartition_pullback_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (s : Finset α) (Q : Finpartition (s.map f)) :
    embeddingPartition f (pullbackEmbeddingPartition f s Q) = Q := by
  let P := embeddingPartition f (pullbackEmbeddingPartition f s Q)
  have hp (a : α) (ha : a ∈ s) : P.part (f a) = Q.part (f a) :=
    embeddingPartition_pullback_part f s Q ha
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨b, hb⟩ := P.nonempty_of_mem_parts hB
    obtain ⟨a, ha, rfl⟩ := mem_map.mp (P.le hB hb)
    have he := (P.part_eq_of_mem hB hb).symm.trans (hp a ha)
    exact (congrArg (fun C : Finset β => C ∈ Q.parts) he).mpr
      (Q.part_mem.mpr (mem_map.mpr ⟨a, ha, rfl⟩))
  · intro hB
    obtain ⟨b, hb⟩ := Q.nonempty_of_mem_parts hB
    obtain ⟨a, ha, rfl⟩ := mem_map.mp (Q.le hB hb)
    have he := (Q.part_eq_of_mem hB hb).symm.trans (hp a ha).symm
    exact (congrArg (fun C : Finset β => C ∈ P.parts) he).mpr
      (P.part_mem.mpr (mem_map.mpr ⟨a, ha, rfl⟩))

noncomputable def embeddingPartitionEquiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (s : Finset α) : Finpartition s ≃ Finpartition (s.map f) :=
  Equiv.ofBijective (embeddingPartition f) ⟨embeddingPartition_injective f s,
    fun Q => ⟨pullbackEmbeddingPartition f s Q, embeddingPartition_pullback_eq f s Q⟩⟩

end WaveTurbulence.Induct
