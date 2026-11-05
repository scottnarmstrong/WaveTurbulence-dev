/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Order.Partition.Finpartition
/-! The finite partition into orbits of an involutive pairing. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

noncomputable def pairingPartition {α : Type*} [Fintype α] [DecidableEq α] (pair : α → α)
    (hinv : Function.Involutive pair) : Finpartition (univ : Finset α) :=
  Finpartition.ofExistsUnique (univ.image (fun x => ({x, pair x} : Finset α)))
    (fun _ _ => subset_univ _) (by
      intro a _
      refine ⟨{a, pair a}, ⟨mem_image.mpr ⟨a, mem_univ _, rfl⟩, mem_insert_self _ _⟩, ?_⟩
      intro B hB
      obtain ⟨x, _, rfl⟩ := mem_image.mp hB.1
      rcases (show a = x ∨ a = pair x from by simpa only [mem_insert, mem_singleton] using hB.2) with h | h
      · subst a
        rfl
      · subst a
        rw [hinv x]
        exact Finset.pair_comm _ _) (by
      intro he
      obtain ⟨x, _, hx⟩ := mem_image.mp he
      exact Finset.notMem_empty x (hx ▸ mem_insert_self x {pair x}))

theorem pairingPartition_mem_parts {α : Type*} [Fintype α] [DecidableEq α] (pair : α → α)
    (hinv : Function.Involutive pair) (B : Finset α) :
    B ∈ (pairingPartition pair hinv).parts ↔ ∃ x, B = {x, pair x} := by
  change B ∈ univ.image (fun x => ({x, pair x} : Finset α)) ↔ _
  simp only [mem_image, mem_univ, true_and]
  exact exists_congr (fun _ => eq_comm)

theorem pairingPartition_card_part {α : Type*} [Fintype α] [DecidableEq α] (pair : α → α)
    (hinv : Function.Involutive pair) (hne : ∀ x, pair x ≠ x)
    (B : Finset α) (hB : B ∈ (pairingPartition pair hinv).parts) : B.card = 2 := by
  obtain ⟨x, rfl⟩ := (pairingPartition_mem_parts pair hinv B).mp hB
  exact Finset.card_pair (hne x).symm

theorem pairingPartition_part {α : Type*} [Fintype α] [DecidableEq α] (pair : α → α)
    (hinv : Function.Involutive pair) (a : α) : (pairingPartition pair hinv).part a = {a, pair a} := by
  apply (pairingPartition pair hinv).part_eq_of_mem
  · exact (pairingPartition_mem_parts pair hinv _).mpr ⟨a, rfl⟩
  · exact Finset.mem_insert_self _ _

end WaveTurbulence.Induct
