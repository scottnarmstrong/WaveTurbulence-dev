/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.TruncatedPoisson
public import WaveTurbulence.Foundations.VdCB.FrequencyIntegration

/-!
# Integer frequency normalization in sharp Poisson summation

Subtracting an integer linear phase preserves the actual sampled sum.
The truncation range shifts by the same integer, so its width rather
than the absolute derivative size determines the error.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Sharp Poisson truncation for an arbitrary integer-translated derivative
range. The finite sum is still the actual original exponential sum. -/
theorem norm_sum_sub_truncated_poisson_shift_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b : ℕ} (hab : a ≤ b) (m : ℤ) (N : ℕ)
    (hrange : ∀ x ∈ Icc (a : ℝ) b, (m : ℝ) ≤ deriv f x ∧ deriv f x ≤ m + N)
    (hsecond : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv (deriv f) x) :
    ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
      ∑ ν ∈ Finset.Icc 0 (N : ℤ),
        ∫ x in (a : ℝ)..b, expPhase (f x - ((m : ℝ) + ν) * x)‖ ≤
      (2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) + 1 := by
  have hd := hf.differentiable (by norm_num)
  have hh := norm_sum_sub_truncated_poisson_le (f := fun x => f x - (m : ℝ) * x)
    (hf.sub (contDiff_const.mul contDiff_id)) hab N
    (by
      intro x hx
      rw [deriv_sub_frequency hd]
      obtain ⟨h1, h2⟩ := hrange x hx
      constructor <;> linarith only [h1, h2])
    (by simpa only [deriv_deriv_sub_frequency hf] using hsecond)
  have heq (n : ℕ) : expPhase (f ((n : ℝ) + 1) - (m : ℝ) * ((n : ℝ) + 1)) =
      expPhase (f ((n : ℝ) + 1)) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using expPhase_sub_int_mul_int f m ((n : ℤ) + 1)
  simp_rw [heq] at hh
  convert hh using 1
  congr 2
  apply Finset.sum_congr rfl
  intro ν _
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  congr 1
  ring

end WaveTurbulence.VdCB
