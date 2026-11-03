/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic
/-!
# Unit-interval Euler–Maclaurin remainder

A polynomial-kernel form of the twice integrated trapezoidal error, used for
the circular height sum in NT-CIRCLE-v2 goal 2.
-/

public section

namespace WaveTurbulence.Counting

open MeasureTheory intervalIntegral Set
open scoped Interval
/-- Exact unit-interval Euler–Maclaurin identity with the Bernoulli kernel. -/
theorem unit_trapezoid_remainder (f g j : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x ∈ [[a,a+1]], HasDerivAt f (g x) x)
    (hg : ∀ x ∈ [[a,a+1]], HasDerivAt g (j x) x)
    (hi : IntervalIntegrable g volume a (a+1))
    (hj : IntervalIntegrable j volume a (a+1)) :
    (f a + f (a+1))/2 - (∫ x in a..a+1, f x) =
      -(∫ x in a..a+1, ((x-a)*(x-a-1)/2) * j x) := by
  let p : ℝ → ℝ := fun x => x-a-1/2
  let q : ℝ → ℝ := fun x => (x-a)*(x-a-1)/2
  have hp (x : ℝ) : HasDerivAt p 1 x := by
    simpa only [p] using! ((hasDerivAt_id x).sub_const a).sub_const (1/2)
  have hq (x : ℝ) : HasDerivAt q (p x) x := by
    convert (((hasDerivAt_id x).sub_const a).mul
      (((hasDerivAt_id x).sub_const a).sub_const 1)).div_const 2 using 1 <;> dsimp [q,p]; ring
  have h1 := integral_mul_deriv_eq_deriv_mul
    (fun x (_ : x ∈ [[a,a+1]]) => hp x) hf
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume a (a+1)) hi
  have h2 := integral_mul_deriv_eq_deriv_mul
    (fun x (_ : x ∈ [[a,a+1]]) => hq x) hg
    (((continuous_id.sub continuous_const).sub continuous_const).intervalIntegrable a (a+1)) hj
  simp only [p, q, sub_self, zero_mul, zero_div, add_sub_cancel_left,
    mul_zero, one_mul] at h1 h2
  linarith

/-- The unit-interval Bernoulli kernel has absolute value at most `1/8`. -/
theorem abs_unit_bernoulli_kernel_le (a x : ℝ) (hx : x ∈ Icc a (a+1)) :
    |(x-a)*(x-a-1)/2| ≤ (1:ℝ)/8 := by
  have h0 : 0 ≤ x-a := sub_nonneg.mpr hx.1
  have h1 : x-a ≤ 1 := by linarith only [hx.2]
  rw [abs_of_nonpos (by nlinarith only [mul_nonpos_of_nonneg_of_nonpos h0 (sub_nonpos.mpr h1)] :
    (x-a)*(x-a-1)/2 ≤ 0)]
  nlinarith only [sq_nonneg (x-a-1/2)]

/-- The Euler–Maclaurin remainder is controlled by the integral of the absolute
second derivative, rather than its supremum. -/
theorem abs_unit_trapezoid_remainder_le (f g j : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x ∈ [[a,a+1]], HasDerivAt f (g x) x)
    (hg : ∀ x ∈ [[a,a+1]], HasDerivAt g (j x) x)
    (hi : IntervalIntegrable g volume a (a+1))
    (hj : IntervalIntegrable j volume a (a+1)) :
    |(f a + f (a+1))/2 - (∫ x in a..a+1, f x)| ≤
      (1/8) * ∫ x in a..a+1, |j x| := by
  rw [unit_trapezoid_remainder f g j a hf hg hi hj, abs_neg]
  have hq : Continuous (fun x : ℝ => (x-a)*(x-a-1)/2) := by fun_prop
  calc
    _ ≤ ∫ x in a..a+1, |((x-a)*(x-a-1)/2) * j x| :=
      abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ x in a..a+1, (1/8) * |j x| := by
      apply integral_mono_on (by linarith)
        (hj.continuousOn_mul hq.continuousOn).abs (hj.abs.const_mul (1/8))
      intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_unit_bernoulli_kernel_le a x hx) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

/-- For a concave twice differentiable function, the error is bounded by the
variation of its first derivative across the unit interval. -/
theorem abs_unit_trapezoid_remainder_le_of_nonpos (f g j : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x ∈ [[a,a+1]], HasDerivAt f (g x) x)
    (hg : ∀ x ∈ [[a,a+1]], HasDerivAt g (j x) x)
    (hi : IntervalIntegrable g volume a (a+1))
    (hj : IntervalIntegrable j volume a (a+1))
    (hn : ∀ x ∈ Icc a (a+1), j x ≤ 0) :
    |(f a + f (a+1))/2 - (∫ x in a..a+1, f x)| ≤
      (g a - g (a+1))/8 := by
  have he : (∫ x in a..a+1, |j x|) = g a - g (a+1) := by
    calc
      _ = ∫ x in a..a+1, -j x := by
        apply integral_congr
        intro x hx
        exact abs_of_nonpos (hn x (by simpa only [uIcc_of_le (by linarith : a ≤ a+1)] using hx))
      _ = -(∫ x in a..a+1, j x) := intervalIntegral.integral_neg
      _ = _ := by rw [integral_eq_sub_of_hasDerivAt hg hj]; ring
  have hb := abs_unit_trapezoid_remainder_le f g j a hf hg hi hj
  rw [he] at hb
  simpa only [one_div_mul_eq_div] using hb

/-- The first-derivative variations telescope over consecutive unit intervals. -/
theorem sum_unit_derivative_variation (g : ℝ → ℝ) (a : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (g (a+k) - g (a+(k+1)))/8) =
      (g a - g (a+N))/8 := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, add_zero, sub_self, zero_div]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Summing the local Euler–Maclaurin errors costs only the total decrease
of the first derivative. -/
theorem sum_abs_unit_trapezoid_remainder_le (f g j : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (hf : ∀ x ∈ Icc a (a+N), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a (a+N), HasDerivAt g (j x) x)
    (hi : ContinuousOn g (Icc a (a+N)))
    (hj : ContinuousOn j (Icc a (a+N)))
    (hn : ∀ x ∈ Icc a (a+N), j x ≤ 0) :
    (∑ k ∈ Finset.range N,
      |(f (a+k) + f (a+(k+1)))/2 - (∫ x in a+k..a+(k+1), f x)|) ≤
      (g a - g (a+N))/8 := by
  rw [← sum_unit_derivative_variation g a N]
  apply Finset.sum_le_sum
  intro k hk
  have hkN : k+1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
  have hsub : Icc (a+k) (a+k+1) ⊆ Icc a (a+N) := by
    intro x hx
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hkn : (k:ℝ)+1 ≤ N := by exact_mod_cast hkN
    constructor <;> linarith only [hx.1, hx.2, hk0, hkn]
  have hle : a+(k:ℝ) ≤ a+k+1 := by linarith
  have hc : [[a+(k:ℝ),a+k+1]] = Icc (a+k) (a+k+1) := uIcc_of_le hle
  have hh := abs_unit_trapezoid_remainder_le_of_nonpos f g j (a+k)
    (fun x hx => hf x (hsub (hc ▸ hx)))
    (fun x hx => hg x (hsub (hc ▸ hx)))
    ((hi.mono hsub).intervalIntegrable_of_Icc hle)
    ((hj.mono hsub).intervalIntegrable_of_Icc hle)
    (fun x hx => hn x (hsub hx))
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hh

/-- The sum of unit trapezoids is the full sample sum with half endpoint
weights removed. -/
theorem sum_unit_trapezoids (f : ℝ → ℝ) (a : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (f (a+k) + f (a+(k+1)))/2) =
      (∑ k ∈ Finset.range (N+1), f (a+k)) - (f a + f (a+N))/2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (n := N+1), ih]
    push_cast
    ring

/-- Euler–Maclaurin on an integer-length interval, with the remainder bounded
by the decrease of the first derivative of a concave function. -/
theorem abs_trapezoid_sum_sub_integral_le (f g j : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (hf : ∀ x ∈ Icc a (a+N), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a (a+N), HasDerivAt g (j x) x)
    (hi : ContinuousOn g (Icc a (a+N)))
    (hj : ContinuousOn j (Icc a (a+N)))
    (hn : ∀ x ∈ Icc a (a+N), j x ≤ 0) :
    |(∑ k ∈ Finset.range (N+1), f (a+k)) - (f a + f (a+N))/2 -
      (∫ x in a..a+N, f x)| ≤ (g a - g (a+N))/8 := by
  have hint : ∀ k < N, IntervalIntegrable f volume (a+k) (a+(k+1)) := by
    intro k hk
    have hsub : Icc (a+(k:ℝ)) (a+(k+1)) ⊆ Icc a (a+N) := by
      intro x hx
      have hkn : (k:ℝ)+1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hk
      have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
      constructor <;> linarith only [hx.1, hx.2, hkn, hk0]
    have hfc : ContinuousOn f (Icc a (a+N)) :=
      fun x hx => (hf x hx).continuousAt.continuousWithinAt
    exact (hfc.mono hsub).intervalIntegrable_of_Icc (by linarith)
  have he := sum_integral_adjacent_intervals (a := fun k : ℕ => a+k) (n := N)
    (fun k hk => by simpa only [Nat.cast_add, Nat.cast_one] using hint k hk)
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, add_zero] at he
  rw [← sum_unit_trapezoids f a N, ← he, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (sum_abs_unit_trapezoid_remainder_le f g j a N hf hg hi hj hn)

end WaveTurbulence.Counting
