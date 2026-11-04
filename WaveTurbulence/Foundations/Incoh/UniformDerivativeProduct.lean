/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Complex.Basic

/-! # Uniform finite operator-derivative bounds for actual products -/

public section
noncomputable section
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- Actual products retain uniform finite derivative bounds with the binomial `2^J` cost. -/
theorem norm_iteratedFDeriv_mul_le_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℂ} {J j : ℕ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbF : ∀ i ≤ J, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hbG : ∀ i ≤ J, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ B) (hj : j ≤ J) (x : E) :
    ‖iteratedFDeriv ℝ j (fun x => f x * g x) x‖ ≤ (2 : ℝ) ^ J * A * B := by
  apply (norm_iteratedFDeriv_mul_le hf hg x (show (j : ℕ∞ω) ≤ ∞ by simp)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hbF i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj) x)
          (Nat.cast_nonneg _))
        (hbG (j - i) ((Nat.sub_le j i).trans hj) x) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ j * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hc : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [hc]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hA) hB

end WaveTurbulence.Incoh
