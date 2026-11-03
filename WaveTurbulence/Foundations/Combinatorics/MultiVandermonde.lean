/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Weighted multivariate Vandermonde

The coordinate-collection step in DH21 Lemma A.4 (`combineq`, L2814–L2822).
-/

public section

namespace WaveTurbulence.Combinatorics
open Finset Polynomial
open scoped Classical
/-- The binomial polynomial expanded over its finite coefficient range. -/
lemma expand_binom (n : ℕ) : (X + 1 : Polynomial ℝ) ^ n =
    ∑ j : Fin (n+1), C (n.choose j : ℝ) * X ^ (j : ℕ) := by
  calc
    _ = ∑ j ∈ range (n+1), C (n.choose j : ℝ) * X ^ j := by
      simpa [mul_comm] using (add_pow (X : Polynomial ℝ) 1 n)
    _ = _ := (Fin.sum_univ_eq_sum_range
      (fun j => C (n.choose j : ℝ) * X ^ j) (n+1)).symm


/-- Product expansion of binomial polynomials over coordinate splits. -/
lemma expand_multi {ι : Type*} [Fintype ι] (ρ : ι → ℕ) :
    (X + 1 : Polynomial ℝ) ^ (∑ i, ρ i) =
    ∑ b : (∀ i, Fin (ρ i + 1)), C (∏ i, (ρ i).choose (b i) : ℝ) *
      X ^ (∑ i, (b i : ℕ)) := by
  rw [← prod_pow_eq_pow_sum]
  simp_rw [expand_binom]
  classical
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro b _
  rw [prod_mul_distrib, prod_pow_eq_pow_sum]
  congr 1
  simp


/-- Weighted multivariate Vandermonde: coordinate splits can be collected by
their total degree, with no loss depending on the number of coordinates. -/
theorem sum_multi_choose_weight {ι : Type*} [Fintype ι] (ρ : ι → ℕ) (f : ℕ → ℝ) :
    ∑ b : (∀ i, Fin (ρ i + 1)), (∏ i, ((ρ i).choose (b i) : ℝ)) *
      f (∑ i, (b i : ℕ)) =
    ∑ B ∈ range ((∑ i, ρ i) + 1), ((∑ i, ρ i).choose B : ℝ) * f B := by
  let L : Polynomial ℝ →ₗ[ℝ] ℝ := Polynomial.lsum (fun n => f n • LinearMap.id)
  have hL (a : ℝ) (n : ℕ) : L (C a * X ^ n) = a * f n := by
    rw [C_mul_X_pow_eq_monomial]
    change ((monomial n) a).sum (fun n a => f n * a) = a * f n
    rw [Polynomial.sum_monomial_index a (fun k c => f k * c) (mul_zero (f n))]
    exact mul_comm _ _
  have h := congrArg L (expand_multi ρ)
  rw [expand_binom] at h
  simp only [map_sum, hL] at h
  have h' := h.symm
  exact h'.trans (Fin.sum_univ_eq_sum_range
    (fun B => ((∑ i, ρ i).choose B : ℝ) * f B) ((∑ i, ρ i) + 1))

end WaveTurbulence.Combinatorics
