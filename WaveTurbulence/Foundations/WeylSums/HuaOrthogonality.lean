/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.GaussianSuperposition
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Orthogonality for Hua's moments

DH21 Lemma A.5 reduces even moments of quadratic exponential sums to counting
integer resonances. This file supplies the finite Fourier orthogonality step.
-/

public section

open MeasureTheory Finset
open scoped BigOperators ComplexConjugate

namespace WaveTurbulence.WeylSums

/-- The additive exponential takes finite sums to finite products. -/
theorem e_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    e (∑ i ∈ S, f i) = ∏ i ∈ S, e (f i) := by
  classical
  induction S using Finset.induction with
  | empty => simp only [sum_empty, e_zero, prod_empty]
  | @insert a S ha ih => rw [sum_insert ha, prod_insert ha, e_add, ih]

theorem conj_e (t : ℝ) : conj (e t) = e (-t) := by
  rw [show -t = 0 - t by ring, e_sub, e_zero, one_div, Complex.inv_eq_conj (norm_e t)]

/-- Integral orthogonality of integer frequencies on a unit interval. -/
theorem integral_e_int (k : ℤ) :
    (∫ t : ℝ in 0..1, e ((k : ℝ) * t)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp only [hk, Int.cast_zero, zero_mul, e_zero, ite_true,
      intervalIntegral.integral_const, sub_zero, one_smul]
  rw [ite_eq_right hk]
  let c : ℂ := ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero _ Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (Int.cast_ne_zero.mpr hk))
  have heq (t : ℝ) : e ((k : ℝ) * t) = Complex.exp (c * t) := by
    unfold e c
    congr 1
    push_cast
    ring
  simp_rw [heq]
  rw [integral_exp_mul_complex hc]
  have hce : Complex.exp c = 1 := by
    exact e_int k
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, hce,
    Complex.exp_zero, sub_self, zero_div]

/-- Finite exponential polynomial with integer frequencies. -/
@[expose] noncomputable def integerExponentialSum {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (freq : ι → ℤ) (t : ℝ) : ℂ :=
  ∑ i : ι, c i * e ((freq i : ℝ) * t)

/-- Number of pairs of equal integer frequencies, including multiplicities. -/
@[expose] noncomputable def resonanceCard {ι : Type*} [Fintype ι] (freq : ι → ℤ) : ℕ :=
  ((univ : Finset (ι × ι)).filter (fun p => freq p.1 = freq p.2)).card

/-- Exact second-moment identity for a finite exponential polynomial. -/
theorem integral_integerExponentialSum_norm_sq {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (freq : ι → ℤ) :
    ((∫ t : ℝ in 0..1, ‖integerExponentialSum c freq t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i : ι, ∑ j : ι, if freq i = freq j then c i * conj (c j) else 0 := by
  classical
  have hpoint (t : ℝ) : ((‖integerExponentialSum c freq t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i : ι, ∑ j : ι, (c i * conj (c j)) * e (((freq i - freq j : ℤ) : ℝ) * t) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    unfold integerExponentialSum
    rw [map_sum, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [map_mul, conj_e]
    have hp : e ((freq i : ℝ) * t) * e (-((freq j : ℝ) * t)) =
        e (((freq i - freq j : ℤ) : ℝ) * t) := by
      rw [← e_add]
      congr 1
      push_cast
      ring
    calc
      _ = (c i * conj (c j)) * (e ((freq i : ℝ) * t) * e (-((freq j : ℝ) * t))) := by ring
      _ = _ := by rw [hp]
  have hint (i j : ι) : IntervalIntegrable
      (fun t : ℝ => (c i * conj (c j)) * e (((freq i - freq j : ℤ) : ℝ) * t)) volume 0 1 :=
    (continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hrow (i : ι) : IntervalIntegrable
      (fun t : ℝ => ∑ j : ι, (c i * conj (c j)) * e (((freq i - freq j : ℤ) : ℝ) * t)) volume 0 1 := by
    convert IntervalIntegrable.sum univ (fun j _ => hint i j) using 1
    funext t
    rw [Finset.sum_apply]
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hrow i)]
  apply sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _ => hint i j)]
  apply sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul, integral_e_int]
  by_cases h : freq i = freq j
  · simp only [h, sub_self, ite_true, mul_one]
  · simp only [h, sub_ne_zero.mpr h, ite_false, mul_zero]

/-- Unit-modulus coefficients make the second moment bounded by the number
of resonant pairs; no arithmetic count is assumed. -/
theorem integral_integerExponentialSum_norm_sq_le {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (freq : ι → ℤ) (hc : ∀ i, ‖c i‖ = 1) :
    (∫ t : ℝ in 0..1, ‖integerExponentialSum c freq t‖ ^ 2) ≤ resonanceCard freq := by
  classical
  have hI : 0 ≤ ∫ t : ℝ in 0..1, ‖integerExponentialSum c freq t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  calc
    _ = ‖((∫ t : ℝ in 0..1, ‖integerExponentialSum c freq t‖ ^ 2 : ℝ) : ℂ)‖ :=
      (Complex.norm_of_nonneg hI).symm
    _ = ‖∑ i : ι, ∑ j : ι, if freq i = freq j then c i * conj (c j) else 0‖ := by
      rw [integral_integerExponentialSum_norm_sq]
    _ ≤ ∑ i : ι, ∑ j : ι, ‖if freq i = freq j then c i * conj (c j) else 0‖ :=
      (norm_sum_le _ _).trans (sum_le_sum (fun i _ => norm_sum_le _ _))
    _ = resonanceCard freq := by
      simp only [apply_ite norm, norm_mul, Complex.norm_conj, hc, one_mul, norm_zero]
      rw [← Fintype.sum_prod_type (fun p : ι × ι => if freq p.1 = freq p.2 then (1 : ℝ) else 0)]
      simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one, resonanceCard]

end WaveTurbulence.WeylSums
