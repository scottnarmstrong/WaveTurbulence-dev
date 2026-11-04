/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.OpenFrequencies
public import WaveTurbulence.Foundations.VdCB.PoissonError
public import WaveTurbulence.Foundations.VdCB.FrequencyNormalization

/-!
# Sharp van der Corput truncated Poisson summation

This is the natural-number-endpoint C² version of Titchmarsh Lemma 4.7.
The derivative is decreasing, the frequency window is open at both ends,
and the absolute error is at most `10*(η⁻¹+log(β-α+2))` for `0<η≤1`.
All normalization integers are constructed internally.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Van der Corput's sharp truncated Poisson lemma, in the decreasing
phase-derivative convention. The sum is exactly over `a<n≤b`.
This version assumes global C² regularity and natural-number endpoints. -/
theorem norm_sum_sub_poisson_derivative_range_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b : ℕ} (hab : a ≤ b) {α β η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hrange : ∀ x ∈ Icc (a : ℝ) b, α ≤ deriv f x ∧ deriv f x ≤ β)
    (hsecond : ∀ x ∈ Icc (a : ℝ) b, deriv (deriv f) x ≤ 0) :
    ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n : ℝ) + 1))) -
      ∑ ν ∈ openFrequencies (α - η) (β + η),
        ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)‖ ≤
          10 * (η⁻¹ + Real.log (β - α + 2)) := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  obtain ⟨hα, hβ⟩ := hrange a (left_mem_Icc.mpr habR)
  have hαβ : α ≤ β := hα.trans hβ
  obtain ⟨m, N, hm0, hm1, hN0, hN1, hN⟩ := exists_frequency_normalization (neg_le_neg hαβ)
  have hh := norm_sum_sub_truncated_poisson_margin_neg_le hf hab m N hm0 hm1 hN0 hN1 hη hrange hsecond
  rw [sum_margin_integrals_neg_eq_open m N hm0 hN1 hη1] at hh
  apply hh.trans
  apply poisson_error_le_ten (sub_nonneg.mpr hαβ) hη hη1 N
  linarith only [hN]

end WaveTurbulence.VdCB
