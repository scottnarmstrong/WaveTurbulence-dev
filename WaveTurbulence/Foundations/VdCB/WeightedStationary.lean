/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.QuadraticStationary
public import WaveTurbulence.Foundations.VdCB.QuadraticTaylor

/-!
# Stationary phase with an explicit cubic error

The quadratic main term carries the correct quarter phase. The error is
the sum of an actual third-derivative remainder and a quadratic Fourier
moment remainder. The stationary point is centered at zero in this module.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory
open scoped FourierTransform SchwartzMap

namespace WaveTurbulence.VdCB

private theorem integrable_schwartz_mul_phase (a : 𝓢(ℝ, ℂ)) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun x => a x * expPhase (f x)) := by
  have hc : Continuous (fun x => a x * expPhase (f x)) :=
    a.continuous.mul ((contDiff_expPhase 0).continuous.comp hf)
  apply (a.integrable (μ := volume)).norm.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by rw [norm_mul, norm_expPhase, mul_one]

/-- A Schwartz amplitude times a C³ phase has the stationary quadratic
main term, with separate explicit second- and third-derivative errors. -/
theorem norm_integral_schwartz_stationary_sub_main_le (a : 𝓢(ℝ, ℂ))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (hc : deriv f 0 = 0)
    (hq : 0 < deriv (deriv f) 0) {M : ℝ}
    (hM : ∀ x ∈ Function.support a, ∀ y ∈ uIcc 0 x, |iteratedDeriv 3 f y| ≤ M) :
    ‖(∫ x : ℝ, a x * expPhase (f x)) -
      expPhase (f 0) * (expPhase (1 / 8) / (Real.sqrt (deriv (deriv f) 0) : ℂ)) * a 0‖ ≤
      (Real.pi / 3 * M) * (∫ x : ℝ, ‖x‖ ^ 3 * ‖a x‖) +
      (1 / Real.sqrt (deriv (deriv f) 0)) * (Real.pi / deriv (deriv f) 0) *
        ∫ ξ : ℝ, ‖ξ‖ ^ 2 * ‖𝓕 a ξ‖ := by
  let q := deriv (deriv f) 0
  have ht : Continuous (quadraticTaylor f 0) := by unfold quadraticTaylor; fun_prop
  have hi := (a.integrable_pow_mul volume 3).const_mul (Real.pi / 3 * M)
  have hpoint (x : ℝ) : ‖a x * expPhase (f x) - a x * expPhase (quadraticTaylor f 0 x)‖ ≤
      (Real.pi / 3 * M) * (‖x‖ ^ 3 * ‖a x‖) := by
    by_cases hx : a x = 0
    · simp only [hx, zero_mul, sub_self, norm_zero, mul_zero, le_refl]
    rw [← mul_sub, norm_mul]
    have hh := norm_expPhase_sub_quadraticTaylor_le hf 0 x M
      (hM x (Function.mem_support.mpr hx))
    have hb := mul_le_mul_of_nonneg_left hh (norm_nonneg (a x))
    simpa only [sub_zero, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using hb
  have hlocal : ‖(∫ x : ℝ, a x * expPhase (f x)) -
      ∫ x : ℝ, a x * expPhase (quadraticTaylor f 0 x)‖ ≤
      (Real.pi / 3 * M) * ∫ x : ℝ, ‖x‖ ^ 3 * ‖a x‖ := by
    rw [← integral_sub (integrable_schwartz_mul_phase a hf.continuous)
      (integrable_schwartz_mul_phase a ht)]
    have hh := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hpoint)
    simpa only [integral_const_mul] using hh
  have heq : (∫ x : ℝ, a x * expPhase (quadraticTaylor f 0 x)) =
      expPhase (f 0) * ∫ x : ℝ, a x * expPhase (q * x ^ 2 / 2) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [quadraticTaylor, hc, sub_zero, zero_mul, add_zero, expPhase_add, q]
      rw [show deriv (deriv f) 0 / 2 * x ^ 2 = deriv (deriv f) 0 * x ^ 2 / 2 by ring]
      ring
  rw [heq] at hlocal
  have hquad := norm_integral_schwartz_mul_quadratic_sub_main_le a hq
  have hqmul : ‖expPhase (f 0) * (∫ x : ℝ, a x * expPhase (q * x ^ 2 / 2)) -
      expPhase (f 0) * (expPhase (1 / 8) / (Real.sqrt q : ℂ)) * a 0‖ ≤
      (1 / Real.sqrt q) * (Real.pi / q) * ∫ ξ : ℝ, ‖ξ‖ ^ 2 * ‖𝓕 a ξ‖ := by
    rw [mul_assoc, ← mul_sub, norm_mul, norm_expPhase, one_mul]
    exact hquad
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (expPhase (f 0) * ∫ x : ℝ, a x * expPhase (q * x ^ 2 / 2)) _).trans (add_le_add hlocal hqmul)

end WaveTurbulence.VdCB
