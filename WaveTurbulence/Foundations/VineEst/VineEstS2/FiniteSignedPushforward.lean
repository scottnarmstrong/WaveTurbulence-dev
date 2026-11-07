/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Module.BigOperators

/-! # Exact signed finite pushforward and support cardinality -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2

noncomputable def pushSignedCoeff {α β : Type*} (S : Finset α) (label : α → β) (sign : α → ℤ)
    (b : β) : ℤ := by
  classical
  exact ∑ a ∈ S.filter (fun a => label a = b), sign a

theorem pushSignedCoeff_smul {α β E : Type*} [Fintype β] [AddCommGroup E]
    (S : Finset α) (label : α → β) (sign : α → ℤ) (f : β → E) :
    (∑ a ∈ S, sign a • f (label a)) = ∑ b, pushSignedCoeff S label sign b • f b := by
  classical
  calc
    _ = ∑ b : β, ∑ a ∈ S.filter (fun a => label a = b), sign a • f (label a) :=
      (Finset.sum_fiberwise S label (fun a => sign a • f (label a))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      unfold pushSignedCoeff
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]

open Classical in
theorem pushSignedCoeff_eq_zero_of_not_mem {α β : Type*}
    (S : Finset α) (label : α → β) (sign : α → ℤ) (b : β) (hb : b ∉ S.image label) :
    pushSignedCoeff S label sign b = 0 := by
  classical
  unfold pushSignedCoeff
  apply Finset.sum_eq_zero
  intro a ha
  exact (hb (Finset.mem_image.mpr ⟨a,(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp ha).2⟩)).elim

open Classical in
/-- Combining actual pairs and boundary origins never increases the number
of nonzero coefficients. The map and signs are arbitrary; cancellations help. -/
theorem card_pushSignedCoeff_support_le {α β : Type*} [Fintype β]
    (S : Finset α) (label : α → β) (sign : α → ℤ) :
    (Finset.univ.filter (fun b => pushSignedCoeff S label sign b ≠ 0)).card ≤ S.card := by
  classical
  have hs : Finset.univ.filter (fun b => pushSignedCoeff S label sign b ≠ 0) ⊆ S.image label := by
    intro b hb
    by_contra hn
    exact (Finset.mem_filter.mp hb).2 (pushSignedCoeff_eq_zero_of_not_mem S label sign b hn)
  exact (Finset.card_le_card hs).trans Finset.card_image_le

end WaveTurbulence.VineEstS2
