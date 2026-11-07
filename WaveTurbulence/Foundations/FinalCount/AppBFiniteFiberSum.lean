/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Tactic

/-! # Summing uniform finite-fiber bounds without division -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
open scoped ENNReal

theorem appb_finite_fiber_sum_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (C : ℝ≥0∞)
    (h : ∀ y ∈ S.image f,((S.filter (fun x => f x = y)).card : ℝ≥0∞) ≤ C) :
    (S.card : ℝ≥0∞) ≤ ((S.image f).card : ℝ≥0∞)*C := by
  have hc := card_eq_sum_card_image f S
  calc
    (S.card : ℝ≥0∞) = ∑ y ∈ S.image f,((S.filter (fun x => f x = y)).card : ℝ≥0∞) := by
      exact_mod_cast hc
    _ ≤ ∑ _y ∈ S.image f,C := sum_le_sum h
    _ = _ := by rw [sum_const,nsmul_eq_mul]

end WaveTurbulence.Mole
