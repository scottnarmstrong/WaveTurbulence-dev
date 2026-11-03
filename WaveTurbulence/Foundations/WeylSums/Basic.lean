/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Field.GeomSum

/-!
# Quadratic exponential sums

We use the convention `e(t) = exp(2πit)` and inclusive integer intervals, as
in DH23 equation `huagausssum`. The geometric-series estimate is the first
ingredient in Weyl differencing; no rational-approximation estimate is assumed.
-/

public section

open scoped BigOperators
open Finset

namespace WaveTurbulence.WeylSums

/-- The additive exponential `exp(2πit)`. -/
@[expose] noncomputable def e (t : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

@[simp] theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem norm_e (t : ℝ) : ‖e t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem e_add (s t : ℝ) : e (s + t) = e s * e t := by
  simp only [e, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem e_sub (s t : ℝ) : e (s - t) = e s / e t := by
  simp only [e, mul_sub, Complex.ofReal_sub, sub_mul, Complex.exp_sub]

theorem e_nat_mul (t : ℝ) (n : ℕ) : e ((n : ℝ) * t) = e t ^ n := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A linear exponential sum of `N` terms. -/
@[expose] noncomputable def linearSum (t : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ range N, e (t * j)

/-- DH23 equation `huagausssum`, including both endpoints `h` and `h + n`. -/
@[expose] noncomputable def gaussSum (s r : ℝ) (h : ℤ) (n : ℕ) : ℂ :=
  ∑ p ∈ range (n + 1), e (s * ((h : ℝ) + p) ^ 2 + r * ((h : ℝ) + p))

/-- At zero frequency every summand is one, including both endpoints. -/
theorem gaussSum_zero_phase (h : ℤ) (n : ℕ) :
    gaussSum 0 0 h n = ((n + 1 : ℕ) : ℂ) := by
  simp only [gaussSum, zero_mul, zero_add, e_zero, sum_const, card_range,
    nsmul_eq_mul, mul_one]

/-- The literal `K log K` bound cannot include `K = 1`, for any constant.
The source uses `log L` at a large ambient scale instead. -/
theorem not_gaussSum_bound_log_one (C : ℝ) :
    ¬ ‖gaussSum 0 0 0 1‖ ≤ C * Real.log 1 := by
  rw [gaussSum_zero_phase]
  norm_num


theorem norm_linearSum_le (t : ℝ) (N : ℕ) : ‖linearSum t N‖ ≤ N := by
  calc
    _ ≤ ∑ j ∈ range N, ‖e (t * j)‖ := norm_sum_le _ _
    _ = N := by simp only [norm_e, sum_const, card_range, nsmul_eq_mul, mul_one]

theorem norm_gaussSum_le (s r : ℝ) (h : ℤ) (n : ℕ) :
    ‖gaussSum s r h n‖ ≤ (n : ℝ) + 1 := by
  calc
    _ ≤ ∑ p ∈ range (n + 1), ‖e (s * ((h : ℝ) + p) ^ 2 + r * ((h : ℝ) + p))‖ :=
      norm_sum_le _ _
    _ = (n : ℝ) + 1 := by simp

/-- Translation only changes the linear frequency and multiplies by a unit phase. -/
theorem gaussSum_shift (s r : ℝ) (h : ℤ) (n : ℕ) :
    gaussSum s r h n = e (s * (h : ℝ) ^ 2 + r * h) *
      gaussSum s (r + 2 * s * h) 0 n := by
  simp only [gaussSum, Int.cast_zero, zero_add, mul_sum, ← e_add]
  apply sum_congr rfl
  intro p _
  congr 1
  ring

theorem norm_gaussSum_shift (s r : ℝ) (h : ℤ) (n : ℕ) :
    ‖gaussSum s r h n‖ = ‖gaussSum s (r + 2 * s * h) 0 n‖ := by
  rw [gaussSum_shift, norm_mul, norm_e, one_mul]

/-- The nonresonant geometric-series estimate. Resonances are covered separately
by `norm_linearSum_le`, since division by zero in Lean is total. -/
theorem norm_linearSum_le_geometric (t : ℝ) (N : ℕ) (ht : e t ≠ 1) :
    ‖linearSum t N‖ ≤ 2 / ‖e t - 1‖ := by
  have hsum : linearSum t N = (e t ^ N - 1) / (e t - 1) := by
    simp only [linearSum, mul_comm t, e_nat_mul]
    exact geom_sum_eq ht N
  rw [hsum, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖e t ^ N - 1‖ ≤ ‖e t ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num

end WaveTurbulence.WeylSums
