/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Elementary partition counts

Code a finite partition by choosing one representative of each part. This
bounds its cardinality by `n^n`, and its factorially weighted count by `(2n)!`.
These estimates supply the factorial losses in TARGET's moment–cumulant bounds.
-/

public section

namespace WaveTurbulence.Combinatorics
open Finset
open scoped Classical

variable {ι : Type*} [DecidableEq ι] {s : Finset ι}

/-- Map every index to one fixed chosen representative of its part. -/
@[expose] noncomputable def partitionCode (P : Finpartition s) : s → s := fun a =>
  ⟨Classical.choose (P.part_nonempty.mpr a.property),
    P.part_subset a (Classical.choose_spec (P.part_nonempty.mpr a.property))⟩

lemma partitionCode_mem_part (P : Finpartition s) (a : s) :
    (partitionCode P a : ι) ∈ P.part a :=
  Classical.choose_spec (P.part_nonempty.mpr a.property)

lemma partitionCode_eq_iff (P : Finpartition s) (a b : s) :
    partitionCode P a = partitionCode P b ↔ P.part a = P.part b := by
  constructor
  · intro h
    apply P.eq_of_mem_parts (P.part_mem.mpr a.property) (P.part_mem.mpr b.property)
      (partitionCode_mem_part P a)
    simpa only [h] using partitionCode_mem_part P b
  · intro h
    apply Subtype.ext
    simp only [partitionCode, h]

/-- The representative code determines the partition. -/
theorem partitionCode_injective : Function.Injective (partitionCode (s := s)) := by
  intro P Q h
  have hpart (a : s) : P.part a = Q.part a := by
    ext b
    by_cases hb : b ∈ s
    · rw [P.mem_part_iff_part_eq_part hb a.property,
        Q.mem_part_iff_part_eq_part hb a.property]
      rw [← partitionCode_eq_iff P ⟨b, hb⟩ a, ← partitionCode_eq_iff Q ⟨b, hb⟩ a]
      rw [h]
    · exact iff_of_false (fun hm => hb (P.part_subset a hm))
        (fun hm => hb (Q.part_subset a hm))
  apply Finpartition.ext
  ext A
  constructor
  · intro hA
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hA
    have has := P.le hA ha
    rw [← P.part_eq_of_mem hA ha, hpart ⟨a, has⟩]
    exact Q.part_mem.mpr has
  · intro hA
    obtain ⟨a, ha⟩ := Q.nonempty_of_mem_parts hA
    have has := Q.le hA ha
    rw [← Q.part_eq_of_mem hA ha, ← hpart ⟨a, has⟩]
    exact P.part_mem.mpr has

/-- A set of cardinality `n` has at most `n^n` partitions. -/
theorem card_finpartition_le : Fintype.card (Finpartition s) ≤ s.card ^ s.card := by
  have h := Fintype.card_le_of_injective (partitionCode (s := s)) (partitionCode_injective (s := s))
  simpa using h

/-- A factorially weighted partition count has loss at most `(2n)!`. -/
theorem card_finpartition_mul_factorial_le :
    Fintype.card (Finpartition s) * s.card.factorial ≤ (2 * s.card).factorial := by
  calc
    _ ≤ s.card ^ s.card * s.card.factorial := Nat.mul_le_mul_right _ (card_finpartition_le (s := s))
    _ ≤ (s.card + 1) ^ s.card * s.card.factorial :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega : s.card ≤ s.card + 1) s.card)
    _ ≤ _ := by simpa only [Nat.mul_comm, two_mul] using
      (Nat.factorial_mul_pow_le_factorial (m := s.card) (n := s.card))

end WaveTurbulence.Combinatorics
