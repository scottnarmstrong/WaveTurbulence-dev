/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Order.Partition.Finpartition
/-! Finite partitions transported through exact carrier equivalences. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

noncomputable def finsetOrderEquiv {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β) : Finset α ≃o Finset β where
  toEquiv := e.finsetCongr
  map_rel_iff' := Finset.map_subset_map

noncomputable def mapUnivPartition {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (P : Finpartition (univ : Finset α)) : Finpartition (univ : Finset β) :=
  (P.map (finsetOrderEquiv e)).copy (finsetOrderEquiv e).map_top

theorem mapUnivPartition_parts {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (P : Finpartition (univ : Finset α)) :
    (mapUnivPartition e P).parts = P.parts.map (finsetOrderEquiv e).toEmbedding := rfl

theorem mapUnivPartition_part {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (P : Finpartition (univ : Finset α)) (a : α) :
    (mapUnivPartition e P).part (e a) = (P.part a).map e.toEmbedding := by
  have hm : (P.part a).map e.toEmbedding ∈ (mapUnivPartition e P).parts := by
    rw [mapUnivPartition_parts]
    exact Finset.mem_map.mpr ⟨P.part a, P.part_mem.mpr (mem_univ a), rfl⟩
  exact (mapUnivPartition e P).part_eq_of_mem hm
    (Finset.mem_map.mpr ⟨a, P.mem_part (mem_univ a), rfl⟩)

theorem mapUnivPartition_part_at {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (P : Finpartition (univ : Finset α)) (b : β) :
    (mapUnivPartition e P).part b = (P.part (e.symm b)).map e.toEmbedding := by
  have he := mapUnivPartition_part e P (e.symm b)
  exact (congrArg (mapUnivPartition e P).part (e.apply_symm_apply b)).symm.trans he

theorem mapUnivPartition_mem_part {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (P : Finpartition (univ : Finset α)) (a b : β) :
    b ∈ (mapUnivPartition e P).part a ↔ e.symm b ∈ P.part (e.symm a) := by
  rw [mapUnivPartition_part_at]
  exact Finset.mem_map_equiv

end WaveTurbulence.Induct
