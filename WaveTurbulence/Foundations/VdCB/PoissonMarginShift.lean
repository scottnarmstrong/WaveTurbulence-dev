/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.PoissonMargin
public import WaveTurbulence.Foundations.VdCB.IntegerPhase

/-!
# Sharp Poisson truncation with frequency shift and adjustable margin

The error depends on the width of the normalized derivative range.
The source sum remains the original actual lattice sum.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Integer-normalized van der Corput truncation with arbitrary positive
margin. For `η≤1`, the selected modes are exactly `α-η<m+ν<β+η`. -/
theorem norm_sum_sub_truncated_poisson_margin_shift_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b : ℕ} (hab : a ≤ b) {α β η : ℝ} (m : ℤ) (N : ℕ)
    (hα0 : (m : ℝ) ≤ α) (hα1 : α < m + 1)
    (hβ0 : (m : ℝ) + N - 1 < β) (hβN : β ≤ m + N) (hη : 0 < η)
    (hrange : ∀ x ∈ Icc (a : ℝ) b, α ≤ deriv f x ∧ deriv f x ≤ β)
    (hsecond : ∀ x ∈ Icc (a : ℝ) b, 0 ≤ deriv (deriv f) x) :
    ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
      ∑ ν ∈ marginFrequencies (α - m) (β - m) η N,
        ∫ x in (a : ℝ)..b, expPhase (f x - ((m : ℝ) + ν) * x)‖ ≤
      ((2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) + 1) +
        2 / (Real.pi * η) := by
  have hd := hf.differentiable (by norm_num)
  have hh := norm_sum_sub_truncated_poisson_margin_le (f := fun x => f x - (m : ℝ) * x)
    (hf.sub (contDiff_const.mul contDiff_id)) hab (α := α - m) (β := β - m) N
    (by linarith only [hα0]) (by linarith only [hα1])
    (by linarith only [hβ0]) (by linarith only [hβN]) hη
    (by
      intro x hx
      rw [deriv_sub_frequency hd]
      obtain ⟨h1, h2⟩ := hrange x hx
      constructor <;> linarith only [h1, h2])
    (by simpa only [deriv_deriv_sub_frequency hf] using hsecond)
  rw [sum_expPhase_sub_int_linear f m a b] at hh
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
