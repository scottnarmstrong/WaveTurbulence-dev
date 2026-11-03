/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.BilinearFourierBound

/-!
# A uniform localized bilinear principal-value Fourier estimate

The finite cutoff integral is bounded by `C(d,χ) D R^(2d)`, independently of
both support centers, both Fourier frequencies and the positive cutoff scale.
This is the estimate in DH21 Lemma 6.3(1), on the square torus, for a localized
amplitude with a uniform bound and a Lipschitz bound in the second variable.
-/

public section

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace NNReal ContDiff

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- The finite cutoff integral in DH21 Lemma 6.3(1), with frequencies absorbing `2π`. -/
@[expose] noncomputable def bilinearFourierTruncation (χ : ℝ → ℝ) (μ : ℝ)
    (A : Mom d → Mom d → ℂ) (ξ η : Mom d) : ℂ :=
  ∫ x : Mom d, unitPhase 1 ⟪ξ, x⟫_ℝ * bilinearInvFourierInner χ μ (A x) x η

/-- The constant is independent of the amplitude, centers, radius, frequencies and scale. -/
@[expose] noncomputable def bilinearFourierBoundConst (d : ℕ) (χ : ℝ → ℝ) (C : ℝ) : ℝ :=
  bilinearSliceBoundConst d χ C * localizedInvNormConst d * 2 ^ d

theorem stronglyMeasurable_bilinearFourierInner {A : Mom d → Mom d → ℂ}
    (hA : Continuous (Function.uncurry A)) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    (μ : ℝ) (η : Mom d) :
    StronglyMeasurable (fun x : Mom d => bilinearInvFourierInner χ μ (A x) x η) := by
  refine StronglyMeasurable.integral_prod_right (f := fun x y : Mom d =>
    (((1 - χ (μ * ⟪x, y⟫_ℝ)) / ⟪x, y⟫_ℝ : ℝ) : ℂ) *
      (A x y * unitPhase 1 ⟪η, y⟫_ℝ)) ?_
  apply Continuous.stronglyMeasurable
  exact (Complex.continuous_ofReal.comp ((hχ.continuous_div μ).comp
    (continuous_fst.inner continuous_snd))).mul
      (hA.mul ((continuous_unitPhase 1).comp (continuous_const.inner continuous_snd)))

/-- The localized outer integrand has an integrable inverse-norm majorant. -/
theorem norm_bilinearFourierIntegrand_le
    (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {C μ R : ℝ} {D : ℝ≥0} (hC : ∀ t, |χ t| ≤ C) (hμ : 0 < μ) (hR : 1 ≤ R)
    {A : Mom d → Mom d → ℂ} {a b : Mom d}
    (hL : ∀ x, LipschitzWith D (A x)) (hb : ∀ x y, ‖A x y‖ ≤ D)
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0)
    (ξ η : Mom d) {x : Mom d} (hx : x ≠ 0) :
    ‖unitPhase 1 ⟪ξ, x⟫_ℝ * bilinearInvFourierInner χ μ (A x) x η‖ ≤
      ((D : ℝ) * bilinearSliceBoundConst d χ C * R ^ d) *
        (Metric.ball a (2 * R)).indicator (fun x : Mom d => ‖x‖⁻¹) x := by
  rw [norm_mul, norm_unitPhase, one_mul]
  by_cases hmem : x ∈ Metric.ball a (2 * R)
  · rw [indicator_of_mem hmem]
    exact (norm_bilinearInvFourierInner_le_pow hd hχ hχs hC hμ hR (hL x)
      (hsy x) (hb x) hx η).trans_eq (mul_comm _ _)
  · rw [indicator_of_notMem hmem, mul_zero]
    have hn : 2 * R ≤ ‖x - a‖ := by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hmem
    have hzero : A x = fun _ => 0 := funext fun y => hsx x y (by linarith)
    rw [hzero, bilinearInvFourierInner]
    simp

/-- Both iterated integrals at finite scale are honest integrals. -/
theorem integrable_bilinearFourierTruncation_integrand
    (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {C μ R : ℝ} {D : ℝ≥0} (hC : ∀ t, |χ t| ≤ C) (hμ : 0 < μ) (hR : 1 ≤ R)
    {A : Mom d → Mom d → ℂ} {a b : Mom d} (hA : Continuous (Function.uncurry A))
    (hL : ∀ x, LipschitzWith D (A x)) (hb : ∀ x y, ‖A x y‖ ≤ D)
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0) (ξ η : Mom d) :
    Integrable (fun x : Mom d => unitPhase 1 ⟪ξ, x⟫_ℝ * bilinearInvFourierInner χ μ (A x) x η) := by
  have hi := (integrableOn_ball_inv_norm_center hd a (2 * R)).integrable_indicator measurableSet_ball
  have hm : AEStronglyMeasurable (fun x : Mom d =>
      unitPhase 1 ⟪ξ, x⟫_ℝ * bilinearInvFourierInner χ μ (A x) x η) :=
    (((continuous_unitPhase 1).comp
    (continuous_const.inner continuous_id)).stronglyMeasurable.mul
      (stronglyMeasurable_bilinearFourierInner hA hχ μ η)).aestronglyMeasurable
  refine (hi.const_mul ((D : ℝ) * bilinearSliceBoundConst d χ C * R ^ d)).mono' hm ?_
  filter_upwards [DeltaKernel.ae_ne_zero (by omega : 0 < d)] with x hx
  exact norm_bilinearFourierIntegrand_le hd hχ hχs hC hμ hR hL hb hsx hsy ξ η hx

/-- Uniform finite-scale bilinear estimate, with the exact radius power of DH21 Lemma 6.3(1). -/
theorem norm_bilinearFourierTruncation_le
    (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {C μ R : ℝ} {D : ℝ≥0} (hC : ∀ t, |χ t| ≤ C) (hμ : 0 < μ) (hR : 1 ≤ R)
    {A : Mom d → Mom d → ℂ} {a b : Mom d}
    (hL : ∀ x, LipschitzWith D (A x)) (hb : ∀ x y, ‖A x y‖ ≤ D)
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0) (ξ η : Mom d) :
    ‖bilinearFourierTruncation χ μ A ξ η‖ ≤
      (D : ℝ) * bilinearFourierBoundConst d χ C * R ^ (2 * d) := by
  have hi := (integrableOn_ball_inv_norm_center hd a (2 * R)).integrable_indicator measurableSet_ball
  have hCn : 0 ≤ C := (abs_nonneg (χ 0)).trans (hC 0)
  have hc := bilinearSliceBoundConst_nonneg d χ hCn
  have hcoeff : 0 ≤ (D : ℝ) * bilinearSliceBoundConst d χ C * R ^ d := by positivity
  have hbound : ‖bilinearFourierTruncation χ μ A ξ η‖ ≤
      ((D : ℝ) * bilinearSliceBoundConst d χ C * R ^ d) *
        ∫ x in Metric.ball a (2 * R), ‖x‖⁻¹ := by
    rw [bilinearFourierTruncation, ← integral_indicator measurableSet_ball, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hi.const_mul _) ?_
    filter_upwards [DeltaKernel.ae_ne_zero (by omega : 0 < d)] with x hx
    exact norm_bilinearFourierIntegrand_le hd hχ hχs hC hμ hR hL hb hsx hsy ξ η hx
  refine hbound.trans ((mul_le_mul_of_nonneg_left
    (integral_ball_inv_norm_le_pow hd a (by linarith : 1 ≤ 2 * R)) hcoeff).trans_eq ?_)
  unfold bilinearFourierBoundConst
  rw [mul_pow, show 2 * d = d + d by omega, pow_add]
  ring

end WaveTurbulence.Resonant
