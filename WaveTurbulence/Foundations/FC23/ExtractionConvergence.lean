/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.TensorExtraction
/-! Absolute convergence of simultaneous differences from the same evaluation box. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Polynomial Finset

theorem tensor_extraction_summable {J κ : Type*} [Fintype J]
    (K : κ → ℂ) (Q : κ → J → ℂ[X]) (D : J → ℕ)
    (hD : ∀ j, 0 < D j) (hd : ∀ k j, (Q k j).natDegree ≤ D j)
    (ρ : J → ℝ) (hρ : ∀ j, 0 < ρ j) (a b : J → ℂ) {B : ℝ}
    (H : FC23UniformEvaluationBox K Q ρ B) :
    Summable fun k => K k * ∏ j, ((Q k j).eval (a j) - (Q k j).eval (b j)) := by
  have hm (i : (j : J) → Fin (D j + 1)) (j : J) :
      ρ j * ((i j : ℝ) / D j) ∈ Set.Icc (0 : ℝ) (ρ j) := by
    have hp : (0 : ℝ) < D j := Nat.cast_pos.mpr (hD j)
    have hi : (i j : ℝ) ≤ D j := by exact_mod_cast Nat.le_of_lt_succ (i j).isLt
    exact ⟨mul_nonneg (hρ j).le (div_nonneg (Nat.cast_nonneg _) hp.le),
      (mul_le_mul_of_nonneg_left ((div_le_one hp).mpr hi) (hρ j).le).trans_eq (mul_one _)⟩
  have hh (i : (j : J) → Fin (D j + 1)) :
      Summable (fun k => K k * ∏ j, (Q k j).eval ((ρ j : ℂ) * interpolationNode (D j) (i j))) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, interpolationNode] using
      (H (fun j => ρ j * ((i j : ℝ) / D j)) (hm i)).1
  have ht (k : κ) : K k * ∏ j, ((Q k j).eval (a j) - (Q k j).eval (b j)) =
      ∑ i : (j : J) → Fin (D j + 1),
        (∏ j, differenceWeight (D j) (ρ j) (a j) (b j) (i j)) *
          (K k * ∏ j, (Q k j).eval ((ρ j : ℂ) * interpolationNode (D j) (i j))) := by
    simp_rw [fun j => interpolate_difference (hD j) (Q k j) (hd k j) (hρ j) (a j) (b j)]
    rw [Fintype.prod_sum, mul_sum]
    apply sum_congr rfl
    intro i _
    rw [prod_mul_distrib]
    ring
  simp_rw [ht]
  exact summable_sum (fun i _ => (hh i).mul_left _)
end WaveTurbulence.FC23
