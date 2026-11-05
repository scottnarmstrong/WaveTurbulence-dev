/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FiniteOrderSums
/-! Exact finite order splitting, with the actual high-order tail left as a conditional sum. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem sum_order_le_eq_sum_orders {α : Type*} [Fintype α] (order : α → ℕ)
    (f : α → ℂ) (M : ℕ) :
    (∑ a, if order a ≤ M then f a else 0) =
      ∑ N ∈ range (M + 1), ∑ a, if order a = N then f a else 0 := by
  classical
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  by_cases ha : order a ≤ M
  · rw [ite_eq_left ha]
    symm
    have he : (∑ N ∈ range (M + 1), if order a = N then f a else 0) =
        (if order a = order a then f a else 0) :=
      sum_eq_single_of_mem (order a) (mem_range.mpr (Nat.lt_succ_of_le ha))
        (fun N _ hN => ite_eq_right (Ne.symm hN))
    exact he.trans (ite_eq_left rfl)
  · rw [ite_eq_right ha]
    symm
    apply sum_eq_zero
    intro N hN
    exact ite_eq_right (fun h => ha (h.trans_le (Nat.le_of_lt_succ (mem_range.mp hN))))

theorem sum_eq_sum_orders_add_tail {α : Type*} [Fintype α] (order : α → ℕ)
    (f : α → ℂ) (M : ℕ) :
    (∑ a, f a) = (∑ N ∈ range (M + 1), ∑ a, if order a = N then f a else 0) +
      ∑ a, if M < order a then f a else 0 := by
  rw [← sum_order_le_eq_sum_orders, ← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  by_cases ha : order a ≤ M
  · rw [ite_eq_left ha, ite_eq_right (not_lt.mpr ha), add_zero]
  · rw [ite_eq_right ha, ite_eq_left (lt_of_not_ge ha), zero_add]

end WaveTurbulence.Induct
