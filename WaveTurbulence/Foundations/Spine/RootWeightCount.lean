/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootWeightExpansion
public import WaveTurbulence.Foundations.Spine.PolynomialOrderAbsorption
/-! Exact root-weight expansion costs only C2 per root and one fixed geometric factor in total order. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem exists_root_weight_count_bound (d m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ,
      (1 + (d : ℝ) * (2 * (n : ℝ) + 1) ^ 2) ^ m ≤ C * 2 ^ n := by
  obtain ⟨C, hC, hb⟩ := exists_succ_pow_le_geometric (2 * m)
  let K : ℝ := 1 + 9 * d
  have hK : 1 ≤ K := le_add_of_nonneg_right (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
  refine ⟨K ^ m * C, one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK) hC, ?_⟩
  intro n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
  have hsq : (2 * (n : ℝ) + 1) ^ 2 ≤ 9 * ((n : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  have hbase : 1 + (d : ℝ) * (2 * (n : ℝ) + 1) ^ 2 ≤ K * ((n : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ ((n : ℝ) + 1) ^ 2 + (d : ℝ) * (9 * ((n : ℝ) + 1) ^ 2) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))
      _ = _ := by dsimp only [K]; ring
  calc
    _ ≤ (K * ((n : ℝ) + 1) ^ 2) ^ m := pow_le_pow_left₀ (by positivity) hbase m
    _ = K ^ m * ((n : ℝ) + 1) ^ (2 * m) := by rw [mul_pow, ← pow_mul]
    _ ≤ K ^ m * (C * 2 ^ n) := mul_le_mul_of_nonneg_left (hb n) (pow_nonneg (zero_le_one.trans hK) m)
    _ = _ := by ring

theorem root_weight_count_product_bound {J : Type*} [Fintype J] (d m : ℕ)
    (C : ℝ) (hC : ∀ n : ℕ, (1 + (d : ℝ) * (2 * (n : ℝ) + 1) ^ 2) ^ m ≤ C * 2 ^ n)
    (n : J → ℕ) :
    (∏ j, (1 + (d : ℝ) * (2 * (n j : ℝ) + 1) ^ 2) ^ m) ≤
      C ^ Fintype.card J * 2 ^ (∑ j, n j) := by
  classical
  calc
    _ ≤ ∏ j, C * 2 ^ n j := prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => hC (n j))
    _ = _ := by simp only [prod_mul_distrib, prod_const, card_univ, prod_pow_eq_pow_sum]

end WaveTurbulence.LGSpine
