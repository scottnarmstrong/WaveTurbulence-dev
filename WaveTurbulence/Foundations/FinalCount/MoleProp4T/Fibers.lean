/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Counting through a map with bounded fibers

`#A ≤ #B · F` when a map sends the finite set `A` into `B` and every fiber over `B` has at most `F` points. This is
the counting step behind every deviation bound of DH23 §10 (fix the post decoration, count the removed labels).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp4

theorem encard_le_mul_of_fiber {α β : Type*} {A : Set α} (hA : A.Finite) (f : α → β) (B : Set β)
    (hB : ∀ a ∈ A, f a ∈ B) (F : ℕ∞) (hF : ∀ b ∈ B, {a | a ∈ A ∧ f a = b}.encard ≤ F) :
    A.encard ≤ B.encard * F := by
  classical
  by_cases hF0 : F = 0
  · have hAe : A = ∅ := by
      ext a
      simp only [Set.mem_empty_iff_false, iff_false]
      intro ha
      have h := hF (f a) (hB a ha)
      rw [hF0, nonpos_iff_eq_zero, Set.encard_eq_zero] at h
      exact (Set.eq_empty_iff_forall_notMem.mp h) a ⟨ha, rfl⟩
    simp [hAe]
  by_cases hBf : B.Finite
  · let S := hA.toFinset
    have hS : A = (S : Set α) := hA.coe_toFinset.symm
    have hfib : ∀ b ∈ S.image f, ((S.filter fun a => f a = b).card : ℕ∞) ≤ F := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      have hsub : ((S.filter fun a' => f a' = f a : Finset α) : Set α) = {a' | a' ∈ A ∧ f a' = f a} := by
        ext a'
        simp [S]
      rw [← Set.encard_coe_eq_coe_finsetCard, hsub]
      exact hF (f a) (hB a ((hA.mem_toFinset).mp ha))
    have hcard : (S.card : ℕ∞) ≤ (S.image f).card * F := by
      rw [Finset.card_eq_sum_card_image f S, Nat.cast_sum]
      calc ∑ b ∈ S.image f, ((S.filter fun a => f a = b).card : ℕ∞)
          ≤ ∑ _b ∈ S.image f, F := Finset.sum_le_sum hfib
        _ = (S.image f).card * F := by rw [Finset.sum_const, nsmul_eq_mul]
    have himg : ((S.image f).card : ℕ∞) ≤ B.encard := by
      rw [← Set.encard_coe_eq_coe_finsetCard]
      apply Set.encard_le_encard
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_coe.mp hb |> Finset.mem_image.mp
      exact hB a ((hA.mem_toFinset).mp ha)
    rw [hS, Set.encard_coe_eq_coe_finsetCard]
    exact hcard.trans (mul_le_mul_left himg F)
  · rw [Set.Infinite.encard_eq hBf, ENat.top_mul hF0]
    exact le_top

end WaveTurbulence.MoleProp4
