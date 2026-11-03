/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.CentralFourier
public import WaveTurbulence.Foundations.Resonant.PrincipalValueRemainder
public import WaveTurbulence.Foundations.Resonant.PrincipalValueComplex
public import WaveTurbulence.Foundations.Resonant.PrincipalValueSlices

/-!
# A frequency-uniform one-dimensional principal-value Fourier bound

The test function's Lipschitz bound and `L¹` norm control an integrable
remainder. The value at zero multiplies the central sine integral, whose
bound is independent of frequency and truncation scale. This is the analytic
one-dimensional ingredient for DH21 Lemma 6.3.
-/

public section

open MeasureTheory Filter Topology Set
open scoped NNReal ContDiff

namespace WaveTurbulence

/-- Uniform bound without differentiating the Fourier phase. -/
theorem norm_pvFourierTruncation_le {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    (hs : ContDiff ℝ 1 χ) {f : ℝ → ℂ} {K : ℝ≥0} {C μ : ℝ}
    (hf : Integrable f) (hL : LipschitzWith K f) (hC : ∀ t, |χ t| ≤ C)
    (hμ : 0 < μ) (η : ℝ) :
    ‖pvTruncationComplex χ μ (fun u => f u * unitPhase η u)‖ ≤
      (1 + C) * (2 * K + ∫ u : ℝ, ‖f u‖) +
        ‖f 0‖ * (6 * (1 + C + ∫ u : ℝ, |deriv χ u|)) := by
  let q : ℝ → ℝ := fun u => (1 - χ (μ * u)) / u
  let z : ℝ → ℂ := fun u => (q u : ℂ) * unitPhase η u
  let c : ℝ → ℂ := (Icc (-1 : ℝ) 1).indicator z
  let r : ℝ → ℂ := fun u => ((1 - χ (μ * u) : ℝ) : ℂ) *
    pvRemainder f u * unitPhase η u
  have hCn : 0 ≤ C := (abs_nonneg (χ 0)).trans (hC 0)
  have hzc : Continuous z :=
    (Complex.continuous_ofReal.comp (hχ.continuous_div μ)).mul (continuous_unitPhase η)
  have hic : Integrable c := hzc.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hir : Integrable r := by
    have hr := integrable_pvRemainder hf hL
    have hp := hr.mul_bdd (g := fun u => ((1 - χ (μ * u) : ℝ) : ℂ) * unitPhase η u)
      (c := (1 + C))
      ((Complex.continuous_ofReal.comp
        (continuous_const.sub (hχ.cont.comp (continuous_const.mul continuous_id)))).mul
          (continuous_unitPhase η)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    · refine hp.congr (Eventually.of_forall fun u => ?_)
      dsimp [r]
      ring
    · rw [norm_mul, norm_unitPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by simpa using add_le_add_left (hC (μ * u)) 1)
  have heq : (fun u => (q u : ℂ) * (f u * unitPhase η u)) =
      fun u => r u + f 0 * c u := by
    funext u
    by_cases hu : u ∈ Icc (-1 : ℝ) 1
    · simp only [r, c, q, pvRemainder, indicator_of_mem hu, z, Complex.real_smul,
        Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    · simp only [r, c, q, pvRemainder, indicator_of_notMem hu, z, sub_zero, mul_zero,
        add_zero, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_inv,
        Complex.ofReal_sub, Complex.ofReal_one]
      ring
  have hcval : ∫ u : ℝ, c u = ∫ u in (-1 : ℝ)..1, z u := by
    dsimp only [c]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hrv : ‖∫ u, r u‖ ≤ (1 + C) * (2 * K + ∫ u : ℝ, ‖f u‖) := by
    have hpoint : ∀ u, ‖r u‖ ≤ (1 + C) * ‖pvRemainder f u‖ := by
      intro u
      dsimp [r]
      rw [norm_mul, norm_mul, norm_unitPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        ((abs_sub _ _).trans (by simpa using add_le_add_left (hC (μ * u)) 1)) (norm_nonneg _)
    have hn : ‖∫ u, r u‖ ≤ (1 + C) * ∫ u, ‖pvRemainder f u‖ := by
      rw [← integral_const_mul]
      exact norm_integral_le_of_norm_le ((integrable_pvRemainder hf hL).norm.const_mul _)
        (Eventually.of_forall hpoint)
    exact hn.trans (mul_le_mul_of_nonneg_left (integral_norm_pvRemainder_le hf hL) (by positivity))
  unfold pvTruncationComplex
  change ‖∫ u, (q u : ℂ) * (f u * unitPhase η u)‖ ≤ _
  rw [heq, integral_add hir (hic.const_mul (f 0)), integral_const_mul, hcval]
  exact (norm_add_le _ _).trans (add_le_add hrv (by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_centralFourier_le hχ hs hC hμ η) (norm_nonneg _)))

end WaveTurbulence
