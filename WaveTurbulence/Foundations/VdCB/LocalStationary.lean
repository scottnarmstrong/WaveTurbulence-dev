/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.QuadraticTaylor

/-!
# Local quadratic approximation of a stationary integral

A bound `M` on the actual third derivative gives an explicit local error
`(2π/3) M r⁴`. The complementary nonstationary tails and the Fresnel
constant are separate ingredients, not hypotheses of this comparison.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Integrating the cubic Taylor phase error on a radius-`r` interval. -/
theorem norm_integral_sub_quadraticTaylor_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (c : ℝ) {r M : ℝ} (hr : 0 ≤ r) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc (c - r) (c + r), |iteratedDeriv 3 f x| ≤ M) :
    ‖(∫ x in c - r..c + r, expPhase (f x)) -
      ∫ x in c - r..c + r, expPhase (quadraticTaylor f c x)‖ ≤
        2 * Real.pi / 3 * M * r ^ 4 := by
  have hcf : Continuous (fun x => expPhase (f x)) := (contDiff_expPhase 0).continuous.comp hf.continuous
  have hcq : Continuous (fun x => expPhase (quadraticTaylor f c x)) := by
    apply (contDiff_expPhase 0).continuous.comp
    unfold quadraticTaylor
    fun_prop
  rw [← intervalIntegral.integral_sub (hcf.intervalIntegrable _ _) (hcq.intervalIntegrable _ _)]
  have hbound : ∀ x ∈ uIoc (c - r) (c + r),
      ‖expPhase (f x) - expPhase (quadraticTaylor f c x)‖ ≤ Real.pi / 3 * M * r ^ 3 := by
    intro x hx
    rw [uIoc_of_le (by linarith : c - r ≤ c + r)] at hx
    have hx' : x ∈ Icc (c - r) (c + r) := Ioc_subset_Icc_self hx
    have hc : c ∈ Icc (c - r) (c + r) := ⟨by linarith, by linarith⟩
    have hp := norm_expPhase_sub_quadraticTaylor_le hf c x M
      (fun y hy => hM y (ordConnected_Icc.uIcc_subset hc hx' hy))
    have hxr : |x - c| ≤ r := abs_le.mpr ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    exact hp.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxr 3)
      (mul_nonneg (by positivity) hM0))
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [show c + r - (c - r) = 2 * r by ring, abs_of_nonneg (mul_nonneg (by norm_num) hr)] at hh
  convert hh using 1
  ring

/-- At an actual stationary point the linear Taylor term vanishes and
the constant phase factors out of the quadratic integral. -/
theorem norm_integral_sub_stationary_quadratic_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (c : ℝ) (hc : deriv f c = 0) {r M : ℝ} (hr : 0 ≤ r) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc (c - r) (c + r), |iteratedDeriv 3 f x| ≤ M) :
    ‖(∫ x in c - r..c + r, expPhase (f x)) - expPhase (f c) *
      ∫ x in c - r..c + r, expPhase (deriv (deriv f) c / 2 * (x - c) ^ 2)‖ ≤
        2 * Real.pi / 3 * M * r ^ 4 := by
  have hh := norm_integral_sub_quadraticTaylor_le hf c hr hM0 hM
  simp only [quadraticTaylor, hc, zero_mul, add_zero, expPhase_add,
    intervalIntegral.integral_const_mul] at hh
  exact hh

end WaveTurbulence.VdCB
