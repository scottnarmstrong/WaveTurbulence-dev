/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.StencilGain
public import WaveTurbulence.Foundations.FC23.LagrangeCost
/-! Closed interpolation costs. A common total-order degree is permissible
under WTPrefixP because delta is chosen after the moment order. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.FC23
open Finset Polynomial

theorem coefficient_sum_le {D : ℕ} (hD : 0 < D) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    (∑ m ∈ range D, coefficientCost D (m + 1) / ρ ^ (m + 1)) ≤
      (D : ℝ) * (4 * Real.exp 1) ^ D / ρ := by
  have hp : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  calc
    _ ≤ ∑ _m ∈ range D, (4 * Real.exp 1) ^ D / ρ := by
      apply sum_le_sum
      intro m _
      apply div_le_div₀ (by positivity) (coefficientCost_le hD _) hp
      simpa only [pow_one] using pow_le_pow_right₀ hρ (Nat.succ_pos m)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul, mul_div_assoc]

/-- Fully numerical tensor bound, valid for either extraction endpoint. -/
theorem tensor_exponential_gain {J κ : Type*} [Fintype J]
    (K : κ → ℂ) (Q : κ → J → ℂ[X]) (D : J → ℕ)
    (hD : ∀ j, 0 < D j) (hd : ∀ k j, (Q k j).natDegree ≤ D j)
    (ρ : J → ℝ) (hρ : ∀ j, 1 ≤ ρ j) (a : J → ℂ) (ha : ∀ j, ‖a j‖ ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (H : FC23UniformEvaluationBox K Q ρ B) :
    ‖∑' k, K k * ∏ j, ((Q k j).eval (a j) - (Q k j).eval 0)‖ ≤
      (4 * Real.exp 1) ^ (∑ j, D j) * (∏ j, (D j : ℝ) / ρ j) * B := by
  apply (tensor_radius_gain K Q D hD hd ρ (fun j => lt_of_lt_of_le zero_lt_one (hρ j)) a ha hB H).trans
  apply mul_le_mul_of_nonneg_right _ hB
  calc
    _ ≤ ∏ j, (D j : ℝ) * (4 * Real.exp 1) ^ D j / ρ j := by
      apply prod_le_prod₀
      · intro j _
        apply sum_nonneg
        intro m _
        exact div_nonneg (sum_nonneg (fun _ _ => norm_nonneg _))
          (pow_nonneg (zero_le_one.trans (hρ j)) _)
      · intro j _
        exact coefficient_sum_le (hD j) (hρ j)
    _ = _ := by
      simp_rw [show ∀ j, (D j : ℝ) * (4 * Real.exp 1) ^ D j / ρ j =
        (4 * Real.exp 1) ^ D j * ((D j : ℝ) / ρ j) from fun j => by ring]
      rw [prod_mul_distrib, prod_pow_eq_pow_sum]

/-- Common-degree variant uses the existing unsliced family interface.
Its exponential base depends only on the moment order, which precedes delta. -/
theorem tensor_common_degree_gain {w : ℕ} {κ : Type*}
    (K : κ → ℂ) (Q : κ → Fin w → ℂ[X]) {D : ℕ}
    (hD : 0 < D) (hd : ∀ k j, (Q k j).natDegree ≤ D)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (a : Fin w → ℂ) (ha : ∀ j, ‖a j‖ ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (H : FC23UniformEvaluationBox K Q (fun _ => ρ) B) :
    ‖∑' k, K k * ∏ j, ((Q k j).eval (a j) - (Q k j).eval 0)‖ ≤
      (4 * Real.exp 1) ^ (w * D) * ((D : ℝ) / ρ) ^ w * B := by
  simpa only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, prod_const] using
    tensor_exponential_gain K Q (fun _ => D) (fun _ => hD) hd (fun _ => ρ)
      (fun _ => hρ) a ha hB H
end WaveTurbulence.FC23
