/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C5VineA
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.VineIITemplate
import Mathlib.Tactic

/-! # Prop 9.6, case (5): degrees in the half-closed ladder `ladderBonds k` -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

theorem card_filter_sum_range {α : Type*} (p : α → Prop) [DecidablePred p] (t : ℕ → Multiset α) (k : ℕ) :
    Multiset.card (Multiset.filter p (∑ i ∈ range k, t i)) = ∑ i ∈ range k, Multiset.card (Multiset.filter p (t i)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, Multiset.filter_add, Multiset.card_add, ih, sum_range_succ]

/-- The number of bonds of the ladder containing a vertex. -/
def ladderDeg (k j : ℕ) : ℕ := Multiset.card ((ladderBonds k).filter fun e => j ∈ e)

theorem ladderDeg_term (k j i : ℕ) :
    Multiset.card (Multiset.filter (fun e => j ∈ e) (2 • {s(labA k (i + 1), labB k (i + 1))} +
      {s(labA k i, labA k (i + 1))} + {s(labB k i, labB k (i + 1))})) =
    (if j = labA k (i + 1) ∨ j = labB k (i + 1) then 2 else 0) +
      (if j = labA k i ∨ j = labA k (i + 1) then 1 else 0) +
      (if j = labB k i ∨ j = labB k (i + 1) then 1 else 0) := by
  classical
  rw [Multiset.filter_add, Multiset.filter_add, Multiset.card_add, Multiset.card_add]
  simp only [Multiset.filter_nsmul, Multiset.filter_singleton, Sym2.mem_iff]
  by_cases h1 : j = labA k (i + 1) ∨ j = labB k (i + 1) <;> by_cases h2 : j = labA k i ∨ j = labA k (i + 1) <;>
    by_cases h3 : j = labB k i ∨ j = labB k (i + 1) <;> simp [h1, h2, h3]

theorem ladderDeg_eq_sum (k j : ℕ) : ladderDeg k j = (if j = 2 ∨ j = 3 then 3 else 0) +
    ∑ i ∈ range k, ((if j = labA k (i + 1) ∨ j = labB k (i + 1) then 2 else 0) +
      (if j = labA k i ∨ j = labA k (i + 1) then 1 else 0) +
      (if j = labB k i ∨ j = labB k (i + 1) then 1 else 0)) := by
  classical
  unfold ladderDeg ladderBonds
  rw [Multiset.filter_add, Multiset.card_add, card_filter_sum_range]
  simp only [Multiset.filter_nsmul, Multiset.filter_singleton, Sym2.mem_iff, ladderDeg_term]
  by_cases h : j = 2 ∨ j = 3 <;> simp [h]

theorem ladderDeg_end_a (k : ℕ) : ladderDeg k (labA k k) = 3 := by
  rw [ladderDeg_eq_sum]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [labA]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h0 : labA (k' + 1) (k' + 1) = 3 + (k' + 1) := by simp [labA]
    rw [h0, if_neg (by omega), zero_add]
    rw [Finset.sum_eq_single k']
    · simp only [labA, labB]; split_ifs <;> first | omega | simp_all
    · intro i hi hik
      have hi' : i < k' + 1 := mem_range.mp hi
      simp only [labA, labB]
      split_ifs <;> omega
    · intro h; exact absurd (mem_range.mpr (Nat.lt_succ_self k')) h

theorem ladderDeg_end_b (k : ℕ) : ladderDeg k (labB k k) = 3 := by
  rw [ladderDeg_eq_sum]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [labB]
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h0 : labB (k' + 1) (k' + 1) = 3 + (k' + 1) + (k' + 1) := by simp [labB]
    rw [h0, if_neg (by omega), zero_add]
    rw [Finset.sum_eq_single k']
    · simp only [labA, labB]; split_ifs <;> first | omega | simp_all
    · intro i hi hik
      have hi' : i < k' + 1 := mem_range.mp hi
      simp only [labA, labB]
      split_ifs <;> omega
    · intro h; exact absurd (mem_range.mpr (Nat.lt_succ_self k')) h

end WaveTurbulence.FinalCountG8
