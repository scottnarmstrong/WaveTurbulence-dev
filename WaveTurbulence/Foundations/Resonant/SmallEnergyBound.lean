/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.BilinearSliceError
public import WaveTurbulence.Foundations.Resonant.InverseSquareVolume

/-!
# The quantitative small-energy bound

The principal-value limit minus the finite high-energy cutoff is bounded by
`C D R^(2d) μ⁻¹ (1+|η|)`. This proves the quantitative estimate underlying
DH21 Lemma 6.3(2). The dependence on the first Fourier frequency drops out
because its phase is outside the inner integral.
-/

public section

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace NNReal ContDiff

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- Dimension- and cutoff-dependent coefficient for the small-energy estimate. -/
@[expose] noncomputable def smallEnergyBoundConst (d : ℕ) (χ : ℝ → ℝ) : ℝ :=
  (2 ^ (d - 1) * ballVolumeCoeff (d - 1)) * localizedInvNormSqConst d * 2 ^ d *
    ∫ u : ℝ, |χ u|

/-- An inverse-square majorant for the localized small-energy integrand. -/
theorem norm_smallEnergyIntegrand_le
    (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {μ R : ℝ} {D : ℝ≥0} (hμ : 0 < μ) (hR : 1 ≤ R)
    {A : Mom d → Mom d → ℂ} {a b : Mom d}
    (hL : ∀ x, LipschitzWith D (A x)) (hb : ∀ x y, ‖A x y‖ ≤ D)
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0)
    (ξ η : Mom d) {x : Mom d} (hx : x ≠ 0) :
    ‖unitPhase 1 ⟪ξ, x⟫_ℝ *
      (bilinearSliceLimitFormula (A x) x η - bilinearInvFourierInner χ μ (A x) x η)‖ ≤
      ((D : ℝ) * (2 ^ (d - 1) * ballVolumeCoeff (d - 1)) * R ^ d *
        (1 + ‖η‖) * (∫ u : ℝ, |χ u|) * μ⁻¹) *
          (Metric.ball a (2 * R)).indicator (fun x : Mom d => (‖x‖⁻¹) ^ 2) x := by
  rw [norm_mul, norm_unitPhase, one_mul]
  by_cases hmem : x ∈ Metric.ball a (2 * R)
  · rw [indicator_of_mem hmem]
    have hbound := norm_bilinearInvFourierInner_error_le_volume hχ hμ
      (by linarith : 0 < R) (hL x) (hsy x) (hb x) hx η
    have hv := real_volume_perp_ball_two_mul_le hd hx (-perpPart x (-b)) hR
    have hiχ : 0 ≤ ∫ u : ℝ, |χ u| := integral_nonneg fun _ => abs_nonneg _
    have hvol := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv D.coe_nonneg)
        (by positivity : 0 ≤ 1 + ‖η‖)) hiχ
    refine hbound.trans ((mul_le_mul_of_nonneg_left hvol (by positivity)).trans_eq ?_)
    ring
  · rw [indicator_of_notMem hmem, mul_zero]
    have hn : 2 * R ≤ ‖x - a‖ := by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hmem
    have hzero : A x = fun _ => 0 := funext fun y => hsx x y (by linarith)
    rw [hzero]
    simp [bilinearSliceLimitFormula, bilinearInvFourierInner, localizedSlice, pvRemainder]

/-- DH21 Lemma 6.3(2)'s error rate for a localized amplitude, uniform in centers
and the first Fourier frequency and linear in the second Fourier frequency. -/
theorem norm_bilinearFourier_small_energy_le
    (hd : 3 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {μ R : ℝ} {D : ℝ≥0} (hμ : 0 < μ) (hR : 1 ≤ R)
    {A : Mom d → Mom d → ℂ} {a b : Mom d} (hA : Continuous (Function.uncurry A))
    (hL : ∀ x, LipschitzWith D (A x)) (hb : ∀ x y, ‖A x y‖ ≤ D)
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0) (ξ η : Mom d) :
    ‖bilinearFourierLimitFormula A ξ η - bilinearFourierTruncation χ μ A ξ η‖ ≤
      (D : ℝ) * smallEnergyBoundConst d χ * R ^ (2 * d) * μ⁻¹ * (1 + ‖η‖) := by
  obtain ⟨C, hCb⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  have hC : ∀ t, |χ t| ≤ C := by simpa only [Real.norm_eq_abs] using hCb
  have hd2 : 2 ≤ d := by omega
  have hiL := integrable_bilinearFourierLimit_integrand hd2 hχ hχs hC hR hA hL hb hsx hsy ξ η
  have hiF := integrable_bilinearFourierTruncation_integrand hd2 hχ hχs hC hμ hR hA hL hb hsx hsy ξ η
  have he : bilinearFourierLimitFormula A ξ η - bilinearFourierTruncation χ μ A ξ η =
      ∫ x : Mom d, unitPhase 1 ⟪ξ, x⟫_ℝ *
        (bilinearSliceLimitFormula (A x) x η - bilinearInvFourierInner χ μ (A x) x η) := by
    rw [bilinearFourierLimitFormula, bilinearFourierTruncation, ← integral_sub hiL hiF]
    congr 1
    funext x
    ring
  have hi := (integrableOn_ball_inv_norm_sq_center hd a (2 * R)).integrable_indicator measurableSet_ball
  let Q : ℝ := (D : ℝ) * (2 ^ (d - 1) * ballVolumeCoeff (d - 1)) * R ^ d *
    (1 + ‖η‖) * (∫ u : ℝ, |χ u|) * μ⁻¹
  have hP := ballVolumeCoeff_nonneg (d - 1)
  have hiχ : 0 ≤ ∫ u : ℝ, |χ u| := integral_nonneg fun _ => abs_nonneg _
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hbound : ‖bilinearFourierLimitFormula A ξ η - bilinearFourierTruncation χ μ A ξ η‖ ≤
      Q * ∫ x in Metric.ball a (2 * R), (‖x‖⁻¹) ^ 2 := by
    rw [he, ← integral_indicator measurableSet_ball, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hi.const_mul Q) ?_
    filter_upwards [DeltaKernel.ae_ne_zero (by omega : 0 < d)] with x hx
    exact norm_smallEnergyIntegrand_le hd2 hχ hμ hR hL hb hsx hsy ξ η hx
  refine hbound.trans ((mul_le_mul_of_nonneg_left
    (integral_ball_inv_norm_sq_le_pow hd a (by linarith : 1 ≤ 2 * R)) hQ).trans_eq ?_)
  dsimp [Q, smallEnergyBoundConst]
  rw [mul_pow, show 2 * d = d + d by omega, pow_add]
  ring

end WaveTurbulence.Resonant
