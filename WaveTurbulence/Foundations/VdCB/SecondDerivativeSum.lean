/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.NumberTheory.DerivativeTests
public import WaveTurbulence.Foundations.VdCB.Phase

/-!
# Second-derivative sums on the actual source interval

Discarding the final sample makes the landed derivative-test sampling
interval stay inside `[a,b]`. Its cost is exactly one, so no derivative
extension beyond the actual source interval is assumed.
-/

public section

open Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

theorem sum_nat_Ico_succ_eq_Ioc {E : Type*} [AddCommMonoid E] (F : ℕ → E) (a b : ℕ) :
    (∑ n ∈ Finset.Ico a b, F (n + 1)) = ∑ n ∈ Finset.Ioc a b, F n := by
  have hh := Finset.sum_Ico_add' F a b (c := 1)
  have heq : Finset.Ico (a + 1) (b + 1) = Finset.Ioc a b := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  simpa only [heq] using hh

/-- A local second-derivative sum estimate with no source-domain leakage.
This is also the short-interval branch of the direct circle B-process. -/
theorem norm_sum_expPhase_le_of_second_deriv_neg {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b : ℕ} (hab : a ≤ b) {μ C : ℝ} (hμ : 0 < μ) (hC : 1 ≤ C)
    (hcurv : ∀ x ∈ Icc (a : ℝ) b, deriv (deriv f) x ∈ Icc (-(C * μ)) (-μ)) :
    ‖∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))‖ ≤
      8 * (C * ((b : ℝ) - a) * Real.sqrt μ + 1 / Real.sqrt μ) + 1 := by
  have heq : (∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) =
      ∑ n ∈ Finset.Ioc a b, expPhase (f n) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      sum_nat_Ico_succ_eq_Ioc (fun n => expPhase (f n)) a b
  rw [heq]
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp only [Finset.Ioc_self, Finset.sum_empty, norm_zero, sub_self, mul_zero]
    positivity
  have hb1 : 1 ≤ b := by omega
  have hab' : a ≤ b - 1 := by omega
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hbound := van_der_corput_second_derivative_of_neg hab' hμ hC
    (f := f) (f' := deriv f) (f'' := deriv (deriv f))
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hf1.differentiable (by norm_num) x).hasDerivAt)
    (fun x hx => by
      have hbcast : ((b - 1 : ℕ) : ℝ) + 1 = b := by exact_mod_cast Nat.sub_add_cancel hb1
      apply hcurv x
      constructor
      · linarith only [hx.1]
      · linarith only [hx.2, hbcast])
  have hsplit : (∑ n ∈ Finset.Ioc a b, expPhase (f n)) =
      (∑ n ∈ Finset.Ioc a (b - 1), expPhase (f n)) + expPhase (f b) := by
    simpa only [Nat.sub_add_cancel hb1] using Finset.sum_Ioc_succ_top (f := fun n : ℕ => expPhase (f n)) hab'
  rw [hsplit]
  have hlen : ((b - 1 : ℕ) : ℝ) - a ≤ (b : ℝ) - a := by
    have hh : ((b - 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast Nat.sub_le b 1
    linarith only [hh]
  have hscale := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlen (by linarith only [hC] : 0 ≤ C)) (Real.sqrt_nonneg μ)
  calc
    _ ≤ ‖∑ n ∈ Finset.Ioc a (b - 1), expPhase (f n)‖ + ‖expPhase (f b)‖ := norm_add_le _ _
    _ ≤ 8 * (C * (((b - 1 : ℕ) : ℝ) - a) * Real.sqrt μ + 1 / Real.sqrt μ) + 1 := by
      rw [norm_expPhase]
      exact add_le_add hbound le_rfl
    _ ≤ _ := by linarith only [hscale]

end WaveTurbulence.VdCB
