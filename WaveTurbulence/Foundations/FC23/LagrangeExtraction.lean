/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
/-! Real-parameter interpolation for complex-valued polynomial families.
The exact interpolation cost is retained explicitly. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.FC23
open Polynomial Finset

def interpolationNode (D : ℕ) (i : Fin (D + 1)) : ℂ := (i : ℂ) / D

def coefficientCost (D m : ℕ) : ℝ :=
  ∑ i : Fin (D + 1), ‖(Lagrange.basis univ (interpolationNode D) i).coeff m‖

/-- Local polynomial version of uniformity; this is not the geometric FC3 gate. -/
def UniformPolynomialFamily (p : ℂ[X]) (ρ B : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) ρ, ‖p.eval (x : ℂ)‖ ≤ B

theorem interpolationNode_injective {D : ℕ} (hD : 0 < D) :
    Function.Injective (interpolationNode D) := by
  intro i j h
  have hz : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have h' : (i : ℂ) = (j : ℂ) := (div_left_inj' hz).mp h
  apply Fin.ext
  exact_mod_cast h'

theorem coeff_norm_le_cost {D : ℕ} (hD : 0 < D) (p : ℂ[X])
    (hd : p.natDegree ≤ D) {B : ℝ}
    (hb : ∀ i : Fin (D + 1), ‖p.eval (interpolationNode D i)‖ ≤ B) (m : ℕ) :
    ‖p.coeff m‖ ≤ B * coefficientCost D m := by
  have hdeg : p.degree < (univ : Finset (Fin (D + 1))).card := by
    simp only [card_univ, Fintype.card_fin]
    exact (degree_le_of_natDegree_le hd).trans_lt (by exact_mod_cast Nat.lt_succ_self D)
  have hi := Lagrange.eq_interpolate (interpolationNode_injective hD).injOn hdeg
  have hc := congrArg (fun q : ℂ[X] => q.coeff m) hi
  rw [Lagrange.interpolate_apply, finsetSum_coeff] at hc
  simp only [coeff_C_mul] at hc
  rw [hc]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin (D + 1), B * ‖(Lagrange.basis univ (interpolationNode D) i).coeff m‖ := by
      apply sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)
    _ = _ := by rw [← mul_sum]; rfl

/-- Coefficient extraction gains a power of the parameter radius. -/
theorem scaled_coeff_norm_le {D : ℕ} (hD : 0 < D) (p : ℂ[X])
    (hd : p.natDegree ≤ D) {ρ B : ℝ} (hρ : 0 < ρ)
    (hb : UniformPolynomialFamily p ρ B) (m : ℕ) :
    ‖p.coeff m‖ ≤ B * coefficientCost D m / ρ ^ m := by
  let q := p.comp (C (ρ : ℂ) * X)
  have hq : q.natDegree ≤ D := natDegree_le_iff_coeff_eq_zero.mpr fun n hn => by
    rw [comp_C_mul_X_coeff, coeff_eq_zero_of_natDegree_lt (hd.trans_lt hn), zero_mul]
  have he (i : Fin (D + 1)) : ‖q.eval (interpolationNode D i)‖ ≤ B := by
    have hpos : (0 : ℝ) < D := Nat.cast_pos.mpr hD
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hi1 : (i : ℝ) ≤ D := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    have hmem : ρ * ((i : ℝ) / D) ∈ Set.Icc (0 : ℝ) ρ :=
      ⟨mul_nonneg hρ.le (div_nonneg hi0 hpos.le),
        (mul_le_mul_of_nonneg_left ((div_le_one hpos).mpr hi1) hρ.le).trans_eq (mul_one _)⟩
    have hh := hb _ hmem
    simpa only [q, eval_comp, eval_mul, eval_C, eval_X, interpolationNode,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast] using hh
  have hh := coeff_norm_le_cost hD q hq he m
  rw [comp_C_mul_X_coeff, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hρ.le] at hh
  exact (le_div_iff₀ (pow_pos hρ m)).mpr hh

theorem eval_one_sub_zero (p : ℂ[X]) {D : ℕ} (hd : p.natDegree ≤ D) :
    p.eval 1 - p.eval 0 = ∑ m ∈ range D, p.coeff (m + 1) := by
  rw [eval_eq_sum_range' (hd.trans_lt (Nat.lt_succ_self D)) (1 : ℂ)]
  simp only [one_pow, mul_one, ← coeff_zero_eq_eval_zero]
  rw [sum_range_succ']
  ring

/-- Exact one-tree Markov reduction, with its deterministic Lagrange cost.
Bounding that cost by an exponential is a separate numerical step. -/
theorem uniformFamily_difference_le {D : ℕ} (hD : 0 < D) (p : ℂ[X])
    (hd : p.natDegree ≤ D) {ρ B : ℝ} (hρ : 0 < ρ)
    (hb : UniformPolynomialFamily p ρ B) :
    ‖p.eval 1 - p.eval 0‖ ≤
      B * ∑ m ∈ range D, coefficientCost D (m + 1) / ρ ^ (m + 1) := by
  rw [eval_one_sub_zero p hd]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ range D, B * coefficientCost D (m + 1) / ρ ^ (m + 1) :=
      sum_le_sum fun m _ => scaled_coeff_norm_le hD p hd hρ hb (m + 1)
    _ = _ := by simp only [mul_div_assoc, mul_sum]
end WaveTurbulence.FC23
