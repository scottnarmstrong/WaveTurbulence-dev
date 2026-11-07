/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.TensorExtraction
/-! Explicit radius gain for the simultaneous interpolation stencil.
The remaining numerical cost is the finite, defined coefficientCost. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.FC23
open Polynomial Finset

theorem eval_sub_zero_eq (p : ℂ[X]) {D : ℕ} (hd : p.natDegree ≤ D) (x : ℂ) :
    p.eval x - p.eval 0 = ∑ m ∈ range D, p.coeff (m + 1) * x ^ (m + 1) := by
  rw [eval_eq_sum_range' (hd.trans_lt (Nat.lt_succ_self D)) x]
  rw [sum_range_succ']
  simp only [pow_zero, mul_one, ← coeff_zero_eq_eval_zero]
  ring

theorem eval_sub_zero_norm_le (p : ℂ[X]) {D : ℕ} (hd : p.natDegree ≤ D) (x : ℂ) :
    ‖p.eval x - p.eval 0‖ ≤ ∑ m ∈ range D, ‖p.coeff (m + 1)‖ * ‖x‖ ^ (m + 1) := by
  rw [eval_sub_zero_eq p hd]
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, norm_pow])

/-- Both the +1 and -1 endpoint extractions gain the same radius powers. -/
theorem differenceWeight_sum_le {D : ℕ} (hD : 0 < D) {ρ : ℝ} (hρ : 0 < ρ)
    (x : ℂ) (hx : ‖x‖ ≤ 1) :
    (∑ i : Fin (D + 1), ‖differenceWeight D ρ x 0 i‖) ≤
      ∑ m ∈ range D, coefficientCost D (m + 1) / ρ ^ (m + 1) := by
  have hd (i : Fin (D + 1)) : (Lagrange.basis univ (interpolationNode D) i).natDegree ≤ D := by
    rw [Lagrange.natDegree_basis (interpolationNode_injective hD).injOn (mem_univ i)]
    simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel, le_refl]
  have hn (m : ℕ) : ‖x / (ρ : ℂ)‖ ^ m ≤ 1 / ρ ^ m := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le, div_pow]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hx) (pow_nonneg hρ.le m)
  calc
    _ ≤ ∑ i : Fin (D + 1), ∑ m ∈ range D,
        ‖(Lagrange.basis univ (interpolationNode D) i).coeff (m + 1)‖ / ρ ^ (m + 1) := by
      apply sum_le_sum
      intro i _
      unfold differenceWeight
      rw [zero_div]
      apply (eval_sub_zero_norm_le _ (hd i) _).trans
      apply sum_le_sum
      intro m _
      exact (mul_le_mul_of_nonneg_left (hn _) (norm_nonneg _)).trans_eq (mul_one_div _ _)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro m _
      simp only [coefficientCost, div_eq_mul_inv, sum_mul]

/-- The simultaneous extraction gains one factor of the inverse radius per
tree (and all higher powers), before the exponential-cost estimate. -/
theorem tensor_radius_gain {J κ : Type*} [Fintype J]
    (K : κ → ℂ) (Q : κ → J → ℂ[X]) (D : J → ℕ)
    (hD : ∀ j, 0 < D j) (hd : ∀ k j, (Q k j).natDegree ≤ D j)
    (ρ : J → ℝ) (hρ : ∀ j, 0 < ρ j) (a : J → ℂ) (ha : ∀ j, ‖a j‖ ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (H : FC23UniformEvaluationBox K Q ρ B) :
    ‖∑' k, K k * ∏ j, ((Q k j).eval (a j) - (Q k j).eval 0)‖ ≤
      (∏ j, ∑ m ∈ range (D j), coefficientCost (D j) (m + 1) / (ρ j) ^ (m + 1)) * B := by
  apply (tensor_extraction_bound K Q D hD hd ρ hρ a (fun _ => 0) H).trans
  apply mul_le_mul_of_nonneg_right _ hB
  apply prod_le_prod₀
  · intro j _
    exact sum_nonneg fun _ _ => norm_nonneg _
  · intro j _
    exact differenceWeight_sum_le (hD j) (hρ j) (a j) (ha j)
end WaveTurbulence.FC23
