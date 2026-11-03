/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.SharpStationary
public import WaveTurbulence.Foundations.VdCB.FrequencyIntegration

/-!
# The stationary dual sum

Apply sharp stationary phase to each actual frequency-shifted phase.
The resulting main terms are the Legendre phases and curvature weights
of the B-process. Endpoint-frequency selection remains separate.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Subtracting a linear frequency does not change the third derivative. -/
theorem iteratedDeriv_three_sub_frequency {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (ν x : ℝ) :
    iteratedDeriv 3 (fun y => f y - ν * y) x = iteratedDeriv 3 f x := by
  have heq : deriv (deriv (fun y => f y - ν * y)) = deriv (deriv f) :=
    funext (deriv_deriv_sub_frequency hf ν)
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [heq]

/-- The finite stationary part of the B-process, with explicit errors.
Each supplied critical point satisfies the actual equation `f'(cν)=ν`.
The statement assumes no oscillatory estimates or exponent-pair bounds. -/
theorem norm_sum_integral_sub_stationary_dual_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (S : Finset ℤ) (c r : ℤ → ℝ) {a b μ M : ℝ} (hμ : 0 < μ) (hM0 : 0 ≤ M)
    (hcurv : ∀ x ∈ Icc a b, μ ≤ deriv (deriv f) x)
    (hr : ∀ ν ∈ S, 0 < r ν)
    (ha : ∀ ν ∈ S, a ≤ c ν - r ν) (hb : ∀ ν ∈ S, c ν + r ν ≤ b)
    (hc : ∀ ν ∈ S, deriv f (c ν) = ν)
    (hM : ∀ ν ∈ S, ∀ x ∈ Icc (c ν - r ν) (c ν + r ν), |iteratedDeriv 3 f x| ≤ M) :
    ‖(∑ ν ∈ S, ∫ x in a..b, expPhase (f x - (ν : ℝ) * x)) -
      ∑ ν ∈ S, expPhase (f (c ν) - (ν : ℝ) * c ν + 1 / 8) /
        (Real.sqrt (deriv (deriv f) (c ν)) : ℂ)‖ ≤
      ∑ ν ∈ S, (2 * Real.pi / 3 * M * r ν ^ 4 +
        2 / (Real.pi * (deriv (deriv f) (c ν) * r ν)) + 2 / (Real.pi * (μ * r ν))) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hd := hf2.differentiable (by norm_num)
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ν hν
  have hh := norm_integral_stationary_sub_main_le
    (f := fun x => f x - (ν : ℝ) * x) (hf.sub (contDiff_const.mul contDiff_id))
    (hr ν hν) hμ (ha ν hν) (hb ν hν)
    (by rw [deriv_sub_frequency hd, hc ν hν, sub_self])
    (by simpa only [deriv_deriv_sub_frequency hf2] using hcurv) hM0
    (by simpa only [iteratedDeriv_three_sub_frequency hf2] using hM ν hν)
  simpa only [deriv_deriv_sub_frequency hf2] using hh

end WaveTurbulence.VdCB
