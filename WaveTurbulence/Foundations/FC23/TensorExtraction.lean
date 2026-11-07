/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.LagrangeExtraction
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
/-! Exact simultaneous real-parameter interpolation before the decoration sum.
This is the algebraic FC2 boundary; identifying the source flower family and
its norm budget is separate. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.FC23
open Polynomial Finset

/-- The finite real interpolation stencil, applied to any two target values. -/
def differenceWeight (D : ℕ) (ρ : ℝ) (a b : ℂ) (i : Fin (D + 1)) : ℂ :=
  (Lagrange.basis univ (interpolationNode D) i).eval (a / (ρ : ℂ)) -
    (Lagrange.basis univ (interpolationNode D) i).eval (b / (ρ : ℂ))

theorem interpolate_difference {D : ℕ} (hD : 0 < D) (p : ℂ[X])
    (hd : p.natDegree ≤ D) {ρ : ℝ} (hρ : 0 < ρ) (a b : ℂ) :
    p.eval a - p.eval b = ∑ i : Fin (D + 1),
      differenceWeight D ρ a b i * p.eval ((ρ : ℂ) * interpolationNode D i) := by
  let q := p.comp (C (ρ : ℂ) * X)
  have hq : q.natDegree ≤ D := natDegree_le_iff_coeff_eq_zero.mpr fun n hn => by
    rw [comp_C_mul_X_coeff, coeff_eq_zero_of_natDegree_lt (hd.trans_lt hn), zero_mul]
  have hdeg : q.degree < (univ : Finset (Fin (D + 1))).card := by
    simp only [card_univ, Fintype.card_fin]
    exact (degree_le_of_natDegree_le hq).trans_lt (by exact_mod_cast Nat.lt_succ_self D)
  have h := Lagrange.eq_interpolate (interpolationNode_injective hD).injOn hdeg
  have hv (x : ℂ) : q.eval (x / (ρ : ℂ)) = p.eval x := by
    simp only [q, eval_comp, eval_mul, eval_C, eval_X]
    congr 1
    exact mul_div_cancel₀ x (by exact_mod_cast hρ.ne')
  rw [← hv a, ← hv b, h]
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  simp only [q, eval_comp, eval_mul, eval_C, eval_X, differenceWeight]
  ring

variable {J κ : Type*} [Fintype J]

def polynomialFamily (K : κ → ℂ) (Q : κ → J → ℂ[X]) (z : J → ℂ) : ℂ :=
  ∑' k, K k * ∏ j, (Q k j).eval (z j)

/-- Uniformity is asserted for the actual family sum on a real box. It includes
convergence, not a bound for the extracted or cutoff expression. -/
def FC23UniformEvaluationBox (K : κ → ℂ) (Q : κ → J → ℂ[X]) (ρ : J → ℝ) (B : ℝ) : Prop :=
  ∀ z : J → ℝ, (∀ j, z j ∈ Set.Icc (0 : ℝ) (ρ j)) →
    Summable (fun k => K k * ∏ j, (Q k j).eval (z j : ℂ)) ∧
      ‖polynomialFamily K Q (fun j => (z j : ℂ))‖ ≤ B

/-- Tensor interpolation commutes with the actual convergent source sum. -/
theorem tensor_extraction (K : κ → ℂ) (Q : κ → J → ℂ[X])
    (D : J → ℕ) (hD : ∀ j, 0 < D j) (hd : ∀ k j, (Q k j).natDegree ≤ D j)
    (ρ : J → ℝ) (hρ : ∀ j, 0 < ρ j) (a b : J → ℂ)
    (hs : ∀ i : (j : J) → Fin (D j + 1), Summable fun k =>
      K k * ∏ j, (Q k j).eval ((ρ j : ℂ) * interpolationNode (D j) (i j))) :
    (∑' k, K k * ∏ j, ((Q k j).eval (a j) - (Q k j).eval (b j))) =
      ∑ i : (j : J) → Fin (D j + 1),
        (∏ j, differenceWeight (D j) (ρ j) (a j) (b j) (i j)) *
          polynomialFamily K Q (fun j => (ρ j : ℂ) * interpolationNode (D j) (i j)) := by
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
  rw [Summable.tsum_finsetSum (fun i _ => (hs i).mul_left _)]
  simp only [polynomialFamily, tsum_mul_left]

/-- Conditional simultaneous FC2 extraction, with its exact finite stencil cost.
There is one interpolation degree per original tree, so costs multiply before
any common degree majorant is taken. -/
theorem tensor_extraction_bound (K : κ → ℂ) (Q : κ → J → ℂ[X])
    (D : J → ℕ) (hD : ∀ j, 0 < D j) (hd : ∀ k j, (Q k j).natDegree ≤ D j)
    (ρ : J → ℝ) (hρ : ∀ j, 0 < ρ j) (a b : J → ℂ) {B : ℝ}
    (H : FC23UniformEvaluationBox K Q ρ B) :
    ‖∑' k, K k * ∏ j, ((Q k j).eval (a j) - (Q k j).eval (b j))‖ ≤
      (∏ j, ∑ i : Fin (D j + 1), ‖differenceWeight (D j) (ρ j) (a j) (b j) i‖) * B := by
  have hm (i : (j : J) → Fin (D j + 1)) (j : J) :
      ρ j * ((i j : ℝ) / D j) ∈ Set.Icc (0 : ℝ) (ρ j) := by
    have hp : (0 : ℝ) < D j := Nat.cast_pos.mpr (hD j)
    have hi : (i j : ℝ) ≤ D j := by exact_mod_cast Nat.le_of_lt_succ (i j).isLt
    exact ⟨mul_nonneg (hρ j).le (div_nonneg (Nat.cast_nonneg _) hp.le),
      (mul_le_mul_of_nonneg_left ((div_le_one hp).mpr hi) (hρ j).le).trans_eq (mul_one _)⟩
  have hh (i : (j : J) → Fin (D j + 1)) :
      Summable (fun k => K k * ∏ j, (Q k j).eval ((ρ j : ℂ) * interpolationNode (D j) (i j))) ∧
      ‖polynomialFamily K Q (fun j => (ρ j : ℂ) * interpolationNode (D j) (i j))‖ ≤ B := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, interpolationNode] using
      H (fun j => ρ j * ((i j : ℝ) / D j)) (hm i)
  rw [tensor_extraction K Q D hD hd ρ hρ a b (fun i => (hh i).1)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : (j : J) → Fin (D j + 1),
        (∏ j, ‖differenceWeight (D j) (ρ j) (a j) (b j) (i j)‖) * B := by
      apply sum_le_sum
      intro i _
      rw [norm_mul, norm_prod]
      exact mul_le_mul_of_nonneg_left (hh i).2 (prod_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by rw [← sum_mul, Fintype.prod_sum]
end WaveTurbulence.FC23
