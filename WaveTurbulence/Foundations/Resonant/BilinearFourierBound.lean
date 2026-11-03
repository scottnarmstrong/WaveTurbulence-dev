/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.ComplexSlicing
public import WaveTurbulence.Foundations.Resonant.PrincipalValueFourier

/-!
# Uniform Fourier bounds on one bilinear resonance slice

The frequency-uniform one-dimensional estimate applies to each tangential
slice. All amplitude bounds are obtained from its ambient support and
Lipschitz constant; no estimate on the sliced integral is assumed.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal ContDiff

namespace WaveTurbulence

variable {d : ℕ}

/-- A uniform slice bound in terms of the ambient and hyperplane support volumes. -/
theorem norm_bilinearInvFourierInner_le_volume
    {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {C μ R : ℝ} {D : ℝ≥0} (hC : ∀ t, |χ t| ≤ C) (hμ : 0 < μ) (hR : 0 < R)
    {f : Mom d → ℂ} {b : Mom d} (hL : LipschitzWith D f)
    (hs : ∀ y, R < ‖y - b‖ → f y = 0) (hb : ∀ y, ‖f y‖ ≤ D)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) (η : Mom d) :
    ‖bilinearInvFourierInner χ μ f ℓ η‖ ≤ ‖ℓ‖⁻¹ *
      ((1 + C) * (2 * ((D : ℝ) * volume.real (Metric.ball (-perpPart ℓ (-b)) (2 * R))) +
        (D : ℝ) * volume.real (Metric.ball b (2 * R))) +
        ((D : ℝ) * volume.real (Metric.ball (-perpPart ℓ (-b)) (2 * R))) *
          (6 * (1 + C + ∫ u : ℝ, |deriv χ u|))) := by
  let ψ : ↥(ℝ ∙ ℓ)ᗮ → ℂ := fun w => unitPhase 1 ⟪η, (w : Mom d)⟫_ℝ
  have hψc : Continuous ψ :=
    (continuous_unitPhase 1).comp (continuous_const.inner continuous_subtype_val)
  have hψ : ∀ w, ‖ψ w‖ ≤ 1 := fun w => (norm_unitPhase 1 _).le
  have hsi := integrable_localizedSlice hL.continuous hs hℓ hψc hψ
  have hsl := lipschitzWith_localizedSlice hR hL hs hb hℓ hψc hψ
  have hsb := norm_localizedSlice_le hR hs hb hℓ hψ 0
  have hsl1 := integral_norm_localizedSlice_le hR hL.continuous hs hb hℓ hψc hψ
  have hscaled : 0 < μ * ‖ℓ‖ := mul_pos hμ (norm_pos_iff.mpr hℓ)
  have h := norm_pvFourierTruncation_le hχ hχs hsi hsl hC hscaled ⟪η, unitVec ℓ⟫_ℝ
  change ‖pvTruncationComplex χ (μ * ‖ℓ‖) (fun t => localizedSlice f ψ t *
      unitPhase ⟪η, unitVec ℓ⟫_ℝ t)‖ ≤
    (1 + C) * (2 * ((D : ℝ) * volume.real (Metric.ball (-perpPart ℓ (-b)) (2 * R))) +
      ∫ t : ℝ, ‖localizedSlice f ψ t‖) +
      ‖localizedSlice f ψ 0‖ * (6 * (1 + C + ∫ u : ℝ, |deriv χ u|)) at h
  rw [bilinearInvFourierInner_eq hχ μ hL.continuous hs hℓ η, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  have hCn : 0 ≤ C := (abs_nonneg (χ 0)).trans (hC 0)
  have hvar : 0 ≤ ∫ u : ℝ, |deriv χ u| := integral_nonneg fun _ => abs_nonneg _
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
  refine h.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hsl1) (by positivity)) ?_)
  exact mul_le_mul_of_nonneg_right hsb (by positivity)

/-- Explicit constant for the polynomial localized slice bound. -/
@[expose] noncomputable def bilinearSliceBoundConst (d : ℕ) (χ : ℝ → ℝ) (C : ℝ) : ℝ :=
  (1 + C) * (2 * (2 ^ (d - 1) * ballVolumeCoeff (d - 1)) + 2 ^ d * ballVolumeCoeff d) +
    (2 ^ (d - 1) * ballVolumeCoeff (d - 1)) *
      (6 * (1 + C + ∫ u : ℝ, |deriv χ u|))

theorem bilinearSliceBoundConst_nonneg (d : ℕ) (χ : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ bilinearSliceBoundConst d χ C := by
  have hp := ballVolumeCoeff_nonneg (d - 1)
  have ha := ballVolumeCoeff_nonneg d
  have hv : 0 ≤ ∫ u : ℝ, |deriv χ u| := integral_nonneg fun _ => abs_nonneg _
  unfold bilinearSliceBoundConst
  positivity

/-- Uniform in the support center, tangential frequency, normal frequency and cutoff scale. -/
theorem norm_bilinearInvFourierInner_le_pow
    (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (hχs : ContDiff ℝ 1 χ)
    {C μ R : ℝ} {D : ℝ≥0} (hC : ∀ t, |χ t| ≤ C) (hμ : 0 < μ) (hR : 1 ≤ R)
    {f : Mom d → ℂ} {b : Mom d} (hL : LipschitzWith D f)
    (hs : ∀ y, R < ‖y - b‖ → f y = 0) (hb : ∀ y, ‖f y‖ ≤ D)
    {ℓ : Mom d} (hℓ : ℓ ≠ 0) (η : Mom d) :
    ‖bilinearInvFourierInner χ μ f ℓ η‖ ≤
      ‖ℓ‖⁻¹ * ((D : ℝ) * bilinearSliceBoundConst d χ C * R ^ d) := by
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hCn : 0 ≤ C := (abs_nonneg (χ 0)).trans (hC 0)
  have hp := ballVolumeCoeff_nonneg (d - 1)
  have ha := ballVolumeCoeff_nonneg d
  have hv : 0 ≤ ∫ u : ℝ, |deriv χ u| := integral_nonneg fun _ => abs_nonneg _
  have hpow : R ^ (d - 1) ≤ R ^ d := pow_le_pow_right₀ hR (Nat.sub_le d 1)
  have hperp : volume.real (Metric.ball (-perpPart ℓ (-b)) (2 * R)) ≤
      (2 ^ (d - 1) * ballVolumeCoeff (d - 1)) * R ^ d := by
    rw [real_volume_perp_ball_eq hd hℓ _ (by positivity), mul_pow]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) hp).trans_eq (by ring)
  have hamb : volume.real (Metric.ball b (2 * R)) =
      (2 ^ d * ballVolumeCoeff d) * R ^ d := by
    rw [real_volume_mom_ball_eq (by omega) b (by positivity), mul_pow]
    ring
  have hDp := mul_le_mul_of_nonneg_left hperp D.coe_nonneg
  have hDa := congrArg (fun v : ℝ => (D : ℝ) * v) hamb
  refine (norm_bilinearInvFourierInner_le_volume hχ hχs hC hμ hRp hL hs hb hℓ η).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hfirst := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hDp (by norm_num : (0 : ℝ) ≤ 2)) hDa.le)
    (by positivity : 0 ≤ 1 + C)
  have hsecond := mul_le_mul_of_nonneg_right hDp
    (by positivity : 0 ≤ 6 * (1 + C + ∫ u : ℝ, |deriv χ u|))
  refine (add_le_add hfirst hsecond).trans_eq ?_
  unfold bilinearSliceBoundConst
  ring

end WaveTurbulence
