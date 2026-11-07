/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Gardens

/-! # Exact signature counts of plain gardens (TARGET L632) -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Comb
open Finset

/-- A finite sum of ±1 signs is the positive count minus the negative count. -/
theorem sum_sign_eq_counts {ι : Type*} [DecidableEq ι] (S : Finset ι) (sig : ι → ℤˣ) :
    (∑ j ∈ S, ((sig j : ℤˣ) : ℤ)) =
      ((S.filter (fun j => sig j = 1)).card : ℤ) - (S.filter (fun j => sig j = -1)).card := by
  classical
  calc (∑ j ∈ S, ((sig j : ℤˣ) : ℤ)) =
      ∑ j ∈ S, ((if sig j = 1 then (1 : ℤ) else 0) - (if sig j = -1 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        rcases Int.units_eq_one_or (sig j) with h | h <;> simp [h]
    _ = _ := by simp [Finset.sum_sub_distrib]

/-- Positive and negative sign filters partition any finite set. -/
theorem card_sign_filters {ι : Type*} [DecidableEq ι] (S : Finset ι) (sig : ι → ℤˣ) :
    (S.filter (fun j => sig j = 1)).card + (S.filter (fun j => sig j = -1)).card = S.card := by
  classical
  have he : S.filter (fun j => sig j = -1) = S.filter (fun j => ¬ sig j = 1) := by
    ext j
    rcases Int.units_eq_one_or (sig j) with h | h <;> simp [h]
  rw [he]
  exact Finset.card_filter_add_card_filter_not (s := S) (fun j => sig j = 1)

/-- A zero signed sum means exactly half the signs are positive. -/
theorem counts_eq_of_sum_sign_zero {ι : Type*} [DecidableEq ι] (S : Finset ι) (sig : ι → ℤˣ)
    (h : (∑ j ∈ S, ((sig j : ℤˣ) : ℤ)) = 0) :
    (S.filter (fun j => sig j = 1)).card = (S.filter (fun j => sig j = -1)).card ∧
      S.card = 2 * (S.filter (fun j => sig j = 1)).card := by
  rw [sum_sign_eq_counts] at h
  have hc : (S.filter (fun j => sig j = 1)).card = (S.filter (fun j => sig j = -1)).card := by
    exact_mod_cast sub_eq_zero.mp h
  exact ⟨hc, by have hh := card_sign_filters S sig; omega⟩

/-- The balanced-sign and even-width constraints follow from ordinary leaf pairing. -/
theorem plain_signature_counts {w : ℕ} {G : Garden w} (hG : G.IsPlain) :
    (Finset.univ.filter (fun j => G.sig j = 1)).card =
      (Finset.univ.filter (fun j => G.sig j = -1)).card ∧
      w = 2 * (Finset.univ.filter (fun j => G.sig j = 1)).card := by
  have h := counts_eq_of_sum_sign_zero Finset.univ G.sig (balanced_of_plain hG)
  simpa only [Finset.card_univ, Fintype.card_fin] using h

end WaveTurbulence.Comb
