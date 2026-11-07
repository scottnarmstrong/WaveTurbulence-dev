/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Tactic

/-!
# CLASSCOUNT: counting class keys

The number of functions `κ : ι → ℕ` supported on a finite set `s` with `Σ κ = n` is at most `2^{n + |s|}`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset

theorem geom_reflect_le (n : ℕ) : ∑ k ∈ range (n + 1), 2 ^ (n - k) ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have : ∀ k ∈ range (n + 1), 2 ^ (n + 1 - (k + 1)) = 2 ^ (n - k) := fun k _ => by simp
    rw [Finset.sum_congr rfl this]
    simp only [Nat.sub_zero]
    calc ∑ k ∈ range (n + 1), 2 ^ (n - k) + 2 ^ (n + 1) ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by omega
      _ = 2 ^ (n + 1 + 1) := by ring

theorem card_piAntidiag_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (n : ℕ) :
    (Finset.piAntidiag s n).card ≤ 2 ^ (n + s.card) := by
  induction s using Finset.cons_induction generalizing n with
  | empty =>
    rw [Finset.piAntidiag_empty]
    split_ifs <;> simp [Nat.one_le_two_pow]
  | cons i s hi ih =>
    rw [Finset.piAntidiag_cons hi, Finset.card_disjiUnion]
    simp only [Finset.card_map, Finset.card_cons]
    calc ∑ p ∈ antidiagonal n, (Finset.piAntidiag s p.2).card
        ≤ ∑ p ∈ antidiagonal n, 2 ^ (p.2 + s.card) := Finset.sum_le_sum fun p _ => ih p.2
      _ = ∑ k ∈ range (n + 1), 2 ^ ((n - k) + s.card) := by
          rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => 2 ^ (b + s.card))]
      _ = 2 ^ s.card * ∑ k ∈ range (n + 1), 2 ^ (n - k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [pow_add, mul_comm]
      _ ≤ 2 ^ s.card * 2 ^ (n + 1) := Nat.mul_le_mul_left _ (geom_reflect_le n)
      _ = 2 ^ (n + (s.card + 1)) := by rw [← pow_add]; congr 1; omega

end WaveTurbulence.ClassCount
