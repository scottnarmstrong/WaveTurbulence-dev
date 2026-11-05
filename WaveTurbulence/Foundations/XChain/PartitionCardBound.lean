/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.PartitionWeightProduct
/-! A partition is determined by its block at each element, giving a quadratic-exponent count. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem finpartition_part_injective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective (fun P : Finpartition (univ : Finset α) => P.part) := by
  classical
  intro P Q h
  apply Finpartition.ext
  ext B
  constructor
  · intro hB
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hB
    have he := P.part_eq_of_mem hB ha
    have hpq : P.part a = Q.part a := congrFun h a
    rw [← he, hpq]
    exact Q.part_mem.mpr (mem_univ _)
  · intro hB
    obtain ⟨a, ha⟩ := Q.nonempty_of_mem_parts hB
    have he := Q.part_eq_of_mem hB ha
    have hpq : P.part a = Q.part a := congrFun h a
    rw [← he, ← hpq]
    exact P.part_mem.mpr (mem_univ _)

theorem card_finpartitions_le {α : Type*} [Fintype α] [DecidableEq α] :
    Nat.card (Finpartition (univ : Finset α)) ≤ (2 ^ Fintype.card α) ^ Fintype.card α := by
  have h := Nat.card_le_card_of_injective
    (fun P : Finpartition (univ : Finset α) => P.part) finpartition_part_injective
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_finset] using h

end WaveTurbulence.Induct
