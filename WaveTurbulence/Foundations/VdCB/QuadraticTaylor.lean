/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.Phase
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Quadratic Taylor control of an oscillatory phase

The explicit third-derivative remainder is obtained from Taylor's theorem
on the actual segment. This supplies the local comparison in stationary
phase; it is not assumed as an extra stationary-phase hypothesis.
-/

public section

open Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- The quadratic Taylor polynomial with actual first and second derivatives. -/
@[expose] noncomputable def quadraticTaylor (f : ℝ → ℝ) (c x : ℝ) : ℝ :=
  f c + deriv f c * (x - c) + deriv (deriv f) c / 2 * (x - c) ^ 2

private theorem taylorWithinEval_two {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {c x : ℝ} (hcx : c ≠ x) :
    taylorWithinEval f 2 (uIcc c x) c x = quadraticTaylor f c x := by
  have hu := uniqueDiffOn_uIcc hcx
  have h1 := iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu
    (hf.contDiffAt.of_le (by norm_num)) (left_mem_uIcc : c ∈ uIcc c x)
  have h2 := iteratedDerivWithin_eq_iteratedDeriv (n := 2) hu
    (hf.contDiffAt.of_le (by norm_num)) (left_mem_uIcc : c ∈ uIcc c x)
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
    Nat.factorial_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    inv_one, pow_zero, pow_one, one_mul, iteratedDerivWithin_zero,
    h1, h2, iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul]
  unfold quadraticTaylor
  norm_num
  ring

/-- Explicit cubic remainder under a bound on the actual third derivative. -/
theorem abs_sub_quadraticTaylor_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (c x M : ℝ)
    (hM : ∀ y ∈ uIcc c x, |iteratedDeriv 3 f y| ≤ M) :
    |f x - quadraticTaylor f c x| ≤ M * |x - c| ^ 3 / 6 := by
  by_cases hcx : c = x
  · subst x
    norm_num [quadraticTaylor]
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hcx hf.contDiffOn
  rw [taylorWithinEval_two hf hcx] at heq
  rw [heq, abs_div, abs_mul, abs_pow]
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_mul]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hM y (uIoo_subset_uIcc_self hy)) (by positivity)) (by norm_num)

/-- The local phase error, retaining the normalization `2π`. -/
theorem norm_expPhase_sub_quadraticTaylor_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (c x M : ℝ)
    (hM : ∀ y ∈ uIcc c x, |iteratedDeriv 3 f y| ≤ M) :
    ‖expPhase (f x) - expPhase (quadraticTaylor f c x)‖ ≤
      Real.pi / 3 * M * |x - c| ^ 3 := by
  have hh := (norm_expPhase_sub_le (f x) (quadraticTaylor f c x)).trans
    (mul_le_mul_of_nonneg_left (abs_sub_quadraticTaylor_le hf c x M hM) (by positivity : 0 ≤ 2 * Real.pi))
  convert hh using 1
  ring

end WaveTurbulence.VdCB
