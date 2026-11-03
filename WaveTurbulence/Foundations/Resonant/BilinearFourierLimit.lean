/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.BilinearFourier
public import WaveTurbulence.Foundations.Resonant.PrincipalValueFourierLimit

/-!
# Existence and uniform bounds for localized bilinear principal values

The slice limit is independent of the cutoff. The scale-uniform majorant of
the previous module permits dominated convergence in the outer momentum.
Together these prove the finite-cutoff estimate and limit assertion in DH21
Lemma 6.3(1) for localized Lipschitz amplitudes on the square torus.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal ContDiff

namespace WaveTurbulence

variable {d : ℕ}

/-- The cutoff-independent symmetric-remainder formula for one bilinear slice. -/
@[expose] noncomputable def bilinearSliceLimitFormula (f : Mom d → ℂ) (ℓ η : Mom d) : ℂ :=
  let s := localizedSlice f (ℓ := ℓ) (fun w => unitPhase 1 ⟪η, (w : Mom d)⟫_ℝ)
  let ν := ⟪η, unitVec ℓ⟫_ℝ
  (‖ℓ‖⁻¹ : ℝ) * ((∫ u : ℝ, pvRemainder s u * unitPhase ν u) +
    s 0 * (2 * Complex.I * (∫ t in (0 : ℝ)..1, ν * Real.sinc (ν * t) : ℝ)))

/-- The explicit outer formula for the principal-value limit. -/
@[expose] noncomputable def bilinearFourierLimitFormula
    (A : Mom d → Mom d → ℂ) (ξ η : Mom d) : ℂ :=
  ∫ x : Mom d, unitPhase 1 ⟪ξ, x⟫_ℝ * bilinearSliceLimitFormula (A x) x η

/-- Pointwise convergence of a nondegenerate bilinear slice. -/
theorem tendsto_bilinearInvFourierInner
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) {R : ℝ} {D : ℝ≥0} (hR : 0 < R)
    {f : Mom d → ℂ} {b : Mom d} (hL : LipschitzWith D f)
    (hs : ∀ y, R < ‖y - b‖ → f y = 0) (hb : ∀ y, ‖f y‖ ≤ D)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) (η : Mom d) :
    Tendsto (fun μ => bilinearInvFourierInner χ μ f ℓ η) atTop
      (𝓝 (bilinearSliceLimitFormula f ℓ η)) := by
  let ψ : ↥(ℝ ∙ ℓ)ᗮ → ℂ := fun w => unitPhase 1 ⟪η, (w : Mom d)⟫_ℝ
  have hψc : Continuous ψ :=
    (continuous_unitPhase 1).comp (continuous_const.inner continuous_subtype_val)
  have hψ : ∀ w, ‖ψ w‖ ≤ 1 := fun _ => (norm_unitPhase 1 _).le
  have hi := integrable_localizedSlice hL.continuous hs hℓ hψc hψ
  have hl := lipschitzWith_localizedSlice hR hL hs hb hℓ hψc hψ
  have ht := tendsto_pvFourierTruncation_of_lipschitz hχ hi hl ⟪η, unitVec ℓ⟫_ℝ
  have hscale : Tendsto (fun μ : ℝ => μ * ‖ℓ‖) atTop atTop :=
    Tendsto.atTop_mul_const (norm_pos_iff.mpr hℓ) tendsto_id
  exact ((ht.comp hscale).const_mul ((‖ℓ‖⁻¹ : ℝ) : ℂ)).congr fun μ =>
    (bilinearInvFourierInner_eq hχ μ hL.continuous hs hℓ η).symm

/-- Dominated convergence gives the full bilinear principal-value limit. -/
theorem tendsto_bilinearFourierTruncation
    (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {C R : ℝ} {D : ℝ≥0} (hC : ∀ t, |χ t| ≤ C) (hR : 1 ≤ R)
    {A : Mom d → Mom d → ℂ} {a b : Mom d} (hA : Continuous (Function.uncurry A))
    (hL : ∀ x, LipschitzWith D (A x)) (hb : ∀ x y, ‖A x y‖ ≤ D)
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0) (ξ η : Mom d) :
    Tendsto (fun μ => bilinearFourierTruncation χ μ A ξ η) atTop
      (𝓝 (bilinearFourierLimitFormula A ξ η)) := by
  have hi := (integrableOn_ball_inv_norm_center hd a (2 * R)).integrable_indicator measurableSet_ball
  unfold bilinearFourierTruncation bilinearFourierLimitFormula
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ((D : ℝ) * bilinearSliceBoundConst d χ C * R ^ d) *
      (Metric.ball a (2 * R)).indicator (fun x : Mom d => ‖x‖⁻¹) x) ?_ ?_ (hi.const_mul _) ?_
  · refine Eventually.of_forall fun μ => ?_
    exact (((continuous_unitPhase 1).comp
      (continuous_const.inner continuous_id)).stronglyMeasurable.mul
        (stronglyMeasurable_bilinearFourierInner hA hχ μ η)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with μ hμ
    filter_upwards [DeltaKernel.ae_ne_zero (by omega : 0 < d)] with x hx
    exact norm_bilinearFourierIntegrand_le hd hχ hχs hC hμ hR hL hb hsx hsy ξ η hx
  · filter_upwards [DeltaKernel.ae_ne_zero (by omega : 0 < d)] with x hx
    exact (tendsto_bilinearInvFourierInner hχ (by linarith : 0 < R) (hL x) (hsy x) (hb x) hx η).const_mul _

/-- The limit obeys exactly the same uniform constant as all finite truncations. -/
theorem norm_bilinearFourierLimitFormula_le
    (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {C R : ℝ} {D : ℝ≥0} (hC : ∀ t, |χ t| ≤ C) (hR : 1 ≤ R)
    {A : Mom d → Mom d → ℂ} {a b : Mom d} (hA : Continuous (Function.uncurry A))
    (hL : ∀ x, LipschitzWith D (A x)) (hb : ∀ x y, ‖A x y‖ ≤ D)
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0) (ξ η : Mom d) :
    ‖bilinearFourierLimitFormula A ξ η‖ ≤
      (D : ℝ) * bilinearFourierBoundConst d χ C * R ^ (2 * d) := by
  apply le_of_tendsto (tendsto_bilinearFourierTruncation hd hχ hχs hC hR hA hL hb hsx hsy ξ η).norm
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with μ hμ
  exact norm_bilinearFourierTruncation_le hd hχ hχs hC hμ hR hL hb hsx hsy ξ η

/-- Joint existence and uniform bound for the localized bilinear principal value. -/
theorem exists_bilinearFourierTruncation_limit
    (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {C R : ℝ} {D : ℝ≥0} (hC : ∀ t, |χ t| ≤ C) (hR : 1 ≤ R)
    {A : Mom d → Mom d → ℂ} {a b : Mom d} (hA : Continuous (Function.uncurry A))
    (hL : ∀ x, LipschitzWith D (A x)) (hb : ∀ x y, ‖A x y‖ ≤ D)
    (hsx : ∀ x y, R < ‖x - a‖ → A x y = 0)
    (hsy : ∀ x y, R < ‖y - b‖ → A x y = 0) (ξ η : Mom d) :
    ∃ v : ℂ, Tendsto (fun μ => bilinearFourierTruncation χ μ A ξ η) atTop (𝓝 v) ∧
      ‖v‖ ≤ (D : ℝ) * bilinearFourierBoundConst d χ C * R ^ (2 * d) :=
  ⟨_, tendsto_bilinearFourierTruncation hd hχ hχs hC hR hA hL hb hsx hsy ξ η,
    norm_bilinearFourierLimitFormula_le hd hχ hχs hC hR hA hL hb hsx hsy ξ η⟩

end WaveTurbulence
