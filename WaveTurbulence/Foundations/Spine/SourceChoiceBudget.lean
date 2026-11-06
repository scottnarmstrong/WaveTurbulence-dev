/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
/-! Explicit normalization of dyadic choice counts, TARGET L2088 and L2106. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

/-- Each gap/pair table costs at most one common exponential after its logarithmic
scale factors are divided out. The high-regularity constant never enters this budget. -/
theorem source_choice_budget_le_one {T : Type*} [Fintype T] (n S : ℕ) (m : T → ℕ)
    (A B C l : ℝ) (hC : 0 < C) (hl : 0 < l) (hB : 1 ≤ B)
    (hA : 0 ≤ A) (hS : (S : ℝ) ≤ B * l) (hm : ∀ t, m t ≤ 2 * n)
    (hT : (Fintype.card T : ℝ) ≤ A ^ n) (hconst : A * B ^ 2 ≤ C) :
    (∑ t : T, (S : ℝ) ^ m t / (C ^ n * l ^ m t)) ≤ 1 := by
  have hquot : (S : ℝ) / l ≤ B := (div_le_iff₀ hl).mpr hS
  have hcpos : 0 < C ^ n := pow_pos hC _
  have hterm (t : T) : (S : ℝ) ^ m t / (C ^ n * l ^ m t) ≤ B ^ (2 * n) / C ^ n := by
    have he : (S : ℝ) ^ m t / (C ^ n * l ^ m t) = ((S : ℝ) / l) ^ m t / C ^ n := by
      rw [div_pow]
      field_simp
    rw [he]
    apply div_le_div_of_nonneg_right _ hcpos.le
    exact (pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hl.le) hquot _).trans
      (pow_le_pow_right₀ hB (hm t))
  calc
    _ ≤ ∑ _t : T, B ^ (2 * n) / C ^ n := sum_le_sum (fun t _ => hterm t)
    _ = (Fintype.card T : ℝ) * (B ^ (2 * n) / C ^ n) := by simp
    _ ≤ A ^ n * (B ^ (2 * n) / C ^ n) :=
      mul_le_mul_of_nonneg_right hT (by positivity)
    _ = (A * B ^ 2) ^ n / C ^ n := by rw [mul_pow, pow_mul]; ring
    _ ≤ 1 := (div_le_one hcpos).mpr (pow_le_pow_left₀ (by positivity) hconst _)

/-- Summing reciprocal costs over actual scale functions yields the normalized
cardinality expression above. -/
theorem source_choice_budget_sigma {T : Type*} [Fintype T] (n S : ℕ) (m : T → ℕ)
    (C l : ℝ) :
    (∑ i : (t : T) × (Fin (m t) → Fin S), (C ^ n * l ^ m i.1)⁻¹) =
      ∑ t : T, (S : ℝ) ^ m t / (C ^ n * l ^ m t) := by
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro t _
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, div_eq_mul_inv]

end WaveTurbulence.LGSpine
