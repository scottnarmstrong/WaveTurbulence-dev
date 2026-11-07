/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.LagrangeExtraction
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic
/-! Explicit exponential cost for the equispaced real interpolation grid. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.FC23
open Finset Polynomial

private theorem lower_grid_product (n : ℕ) :
    (∏ j ∈ range n, |(n : ℝ) - j|) = n.factorial := by
  rw [← prod_range_reflect]
  calc
    _ = ∏ j ∈ range n, ((j : ℝ) + 1) := by
      apply prod_congr rfl
      intro j hj
      have hj' : j < n := mem_range.mp hj
      rw [Nat.cast_sub (by omega : j ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast
      rw [show (n : ℝ) - (n - 1 - j) = j + 1 by ring, abs_of_nonneg (by positivity)]
    _ = n.factorial := by exact_mod_cast prod_range_add_one_eq_factorial n

theorem grid_denominator (n i : ℕ) (hi : i ≤ n) :
    (∏ j ∈ range (n + 1), if j = i then (1 : ℝ) else |(i : ℝ) - j|) =
      (i.factorial : ℝ) * (n - i).factorial := by
  induction n generalizing i with
  | zero =>
    have : i = 0 := by omega
    subst i
    norm_num
  | succ n ih =>
    by_cases hin : i ≤ n
    · rw [prod_range_succ, ite_eq_right (by omega : n + 1 ≠ i), ih i hin]
      have hd : n + 1 - i = (n - i) + 1 := by omega
      rw [hd, Nat.factorial_succ]
      push_cast
      rw [abs_of_nonpos (by
        have hh : (i : ℝ) ≤ n + 1 := by exact_mod_cast (show i ≤ n + 1 by omega)
        linarith)]
      rw [Nat.cast_sub hin]
      ring
    · have he : i = n + 1 := by omega
      subst i
      rw [prod_range_succ, ite_eq_left rfl, mul_one]
      have hp : (∏ j ∈ range (n + 1), if j = n + 1 then (1 : ℝ) else
          |((n + 1 : ℕ) : ℝ) - j|) = ∏ j ∈ range (n + 1), |((n + 1 : ℕ) : ℝ) - j| := by
        apply prod_congr rfl
        intro j hj
        rw [ite_eq_right (ne_of_lt (mem_range.mp hj))]
      rw [hp, lower_grid_product]
      simp

private theorem mahlerMeasure_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) :
    (∏ i ∈ s, f i).mahlerMeasure = ∏ i ∈ s, (f i).mahlerMeasure := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [prod_insert ha, mahlerMeasure_mul, ih, prod_insert ha]

theorem interpolationNode_norm_le {D : ℕ} (hD : 0 < D) (i : Fin (D + 1)) :
    ‖interpolationNode D i‖ ≤ 1 := by
  rw [interpolationNode, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact (div_le_one (Nat.cast_pos.mpr hD)).mpr (by exact_mod_cast Nat.le_of_lt_succ i.isLt)

theorem basis_mahlerMeasure {D : ℕ} (hD : 0 < D) (i : Fin (D + 1)) :
    (Lagrange.basis univ (interpolationNode D) i).mahlerMeasure =
      (D : ℝ) ^ D / ((i.val.factorial : ℝ) * (D - i.val).factorial) := by
  classical
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  have hnorm (j : Fin (D + 1)) :
      ‖interpolationNode D i - interpolationNode D j‖ = |(i : ℝ) - j| / D := by
    rw [interpolationNode, interpolationNode, ← sub_div, norm_div, Complex.norm_natCast]
    congr 1
    simpa only [Complex.ofReal_sub, Complex.ofReal_natCast, Real.norm_eq_abs] using
      (Complex.norm_real ((i : ℝ) - j))
  rw [Lagrange.basis, mahlerMeasure_finset_prod]
  simp_rw [Lagrange.basisDivisor, mahlerMeasure_mul, mahlerMeasure_const,
    mahlerMeasure_X_sub_C, max_eq_left (interpolationNode_norm_le hD _), mul_one,
    norm_inv, hnorm, inv_div]
  rw [prod_div_distrib]
  have hc : (univ.erase i : Finset (Fin (D + 1))).card = D := by simp
  rw [prod_const, hc]
  congr 1
  calc
    (∏ j ∈ univ.erase i, |(i : ℝ) - j|) =
        ∏ j : Fin (D + 1), if j = i then 1 else |(i : ℝ) - j| := by
      rw [← Finset.prod_erase_mul _ _ (mem_univ i)]
      simp only [ite_true, mul_one]
      apply prod_congr rfl
      intro j hj
      rw [ite_eq_right (mem_erase.mp hj).1]
    _ = ∏ j ∈ range (D + 1), if j = i.val then (1 : ℝ) else |(i : ℝ) - j| := by
      simpa only [Fin.ext_iff] using
        (Fin.prod_univ_eq_prod_range (fun j => if j = i.val then (1 : ℝ) else |(i : ℝ) - j|) (D + 1))
    _ = _ := grid_denominator D i.val (Nat.le_of_lt_succ i.isLt)

/-- The exact cost is a binomial coefficient times the grid factorial ratio. -/
theorem coefficientCost_le_factorial {D : ℕ} (hD : 0 < D) (m : ℕ) :
    coefficientCost D m ≤ (D.choose m : ℝ) * 2 ^ D * ((D : ℝ) ^ D / D.factorial) := by
  classical
  have he (i : Fin (D + 1)) :
      (D : ℝ) ^ D / ((i.val.factorial : ℝ) * (D - i.val).factorial) =
        (D.choose i.val : ℝ) * ((D : ℝ) ^ D / D.factorial) := by
    have hfac : (D.choose i.val : ℝ) * i.val.factorial * (D - i.val).factorial = D.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ i.isLt)
    have h0 : (D.factorial : ℝ) ≠ 0 := by positivity
    have h1 : (i.val.factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((D - i.val).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith only [hfac]
  have hs : (∑ i : Fin (D + 1), (D.choose i.val : ℝ)) = 2 ^ D := by
    calc
      _ = ∑ i ∈ range (D + 1), (D.choose i : ℝ) :=
        Fin.sum_univ_eq_sum_range (fun i => (D.choose i : ℝ)) (D + 1)
      _ = _ := by exact_mod_cast Nat.sum_range_choose D
  calc
    coefficientCost D m ≤ ∑ i : Fin (D + 1),
        (D.choose m : ℝ) * ((D.choose i.val : ℝ) * ((D : ℝ) ^ D / D.factorial)) := by
      apply sum_le_sum
      intro i _
      have hh := (Lagrange.basis univ (interpolationNode D) i).norm_coeff_le_choose_mul_mahlerMeasure m
      simpa only [Lagrange.natDegree_basis (interpolationNode_injective hD).injOn (mem_univ i),
        card_univ, Fintype.card_fin, Nat.add_sub_cancel, basis_mahlerMeasure hD i, he i] using hh
    _ = _ := by rw [← mul_sum, ← sum_mul, hs]; ring

/-- FC2's dimension-free equispaced Lagrange coefficient cost. -/
theorem coefficientCost_le {D : ℕ} (hD : 0 < D) (m : ℕ) :
    coefficientCost D m ≤ (4 * Real.exp 1) ^ D := by
  have hc : (D.choose m : ℝ) ≤ 2 ^ D := by exact_mod_cast Nat.choose_le_two_pow D m
  have he : (D : ℝ) ^ D / D.factorial ≤ (Real.exp 1) ^ D := by
    simpa only [← Real.exp_nat_mul, mul_one] using Real.pow_div_factorial_le_exp (D : ℝ) (Nat.cast_nonneg D) D
  calc
    coefficientCost D m ≤ (D.choose m : ℝ) * 2 ^ D * ((D : ℝ) ^ D / D.factorial) :=
      coefficientCost_le_factorial hD m
    _ ≤ (2 : ℝ) ^ D * 2 ^ D * (Real.exp 1) ^ D :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc (by positivity)) he (by positivity) (by positivity)
    _ = _ := by rw [← mul_pow, ← mul_pow]; norm_num
end WaveTurbulence.FC23
