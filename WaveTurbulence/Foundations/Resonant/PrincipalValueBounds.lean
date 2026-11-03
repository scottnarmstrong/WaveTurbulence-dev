/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.PrincipalValueOneDim
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Elementary principal-value bounds

Compact support and a Lipschitz bound control the symmetric quotient. The
bounds here are independent of the truncation scale, but do not assert the
Fourier-frequency uniformity required in DH21 Lemma 6.3.
-/

public section

open MeasureTheory Filter Topology Set
open scoped NNReal

namespace WaveTurbulence.Resonant

/-- Cancellation removes the singularity, with the Lipschitz constant as bound. -/
theorem abs_pvQuotient_le {f : ℝ → ℝ} {K : ℝ≥0} (hL : LipschitzWith K f)
    {u : ℝ} (hu : u ≠ 0) : |pvQuotient f u| ≤ K := by
  rw [pvQuotient_of_ne f hu, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [div_le_iff₀ (mul_pos (by norm_num) (abs_pos.mpr hu))]
  have h := hL.dist_le_mul u (-u)
  simp only [Real.dist_eq, sub_neg_eq_add, ← two_mul, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  exact h.trans_eq (by ring)

/-- The quotient has the same symmetric support radius as the test function. -/
theorem pvQuotient_eq_zero_of_radius {f : ℝ → ℝ} {R u : ℝ}
    (hR : 0 ≤ R) (hs : ∀ x, R < |x| → f x = 0) (hu : R < |u|) :
    pvQuotient f u = 0 := by
  have hne : u ≠ 0 := by intro he; simpa [he] using hR.trans_lt hu
  rw [pvQuotient_of_ne f hne, hs u hu, hs (-u) (by simpa using hu)]
  simp

/-- An explicit finite bound for the integral of the symmetric quotient. -/
theorem integral_abs_pvQuotient_le {f : ℝ → ℝ} {K : ℝ≥0} {R : ℝ}
    (hc : Continuous f) (hd : DifferentiableAt ℝ f 0) (hf : HasCompactSupport f)
    (hL : LipschitzWith K f) (hR : 0 ≤ R) (hs : ∀ x, R < |x| → f x = 0) :
    (∫ u, |pvQuotient f u|) ≤ 2 * R * K := by
  let B : ℝ → ℝ := (Icc (-R) R).indicator (fun _ => (K : ℝ))
  have hB : Integrable B := by
    exact (integrableOn_const (C := (K : ℝ)) (s := Icc (-R) R)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Icc
  have hbound : ∀ᵐ u : ℝ, |pvQuotient f u| ≤ B u := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
    have hne : u ≠ 0 := by simpa using hu
    by_cases hmem : u ∈ Icc (-R) R
    · dsimp only [B]
      rw [indicator_of_mem hmem]
      exact abs_pvQuotient_le hL hne
    · dsimp only [B]
      rw [indicator_of_notMem hmem]
      have hout : R < |u| := by
        by_contra hn
        exact hmem (abs_le.mp (le_of_not_gt hn))
      rw [pvQuotient_eq_zero_of_radius hR hs hout, abs_zero]
  refine (integral_mono_ae (integrable_pvQuotient hc hd hf).abs hB hbound).trans_eq ?_
  dsimp only [B]
  rw [integral_indicator measurableSet_Icc]
  simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R)]
  ring

/-- Explicit one-dimensional principal-value bound. -/
theorem abs_principalValueOneDim_le_radius {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {f : ℝ → ℝ} {K : ℝ≥0} {R : ℝ}
    (hc : Continuous f) (hd : DifferentiableAt ℝ f 0) (hf : HasCompactSupport f)
    (hL : LipschitzWith K f) (hR : 0 ≤ R) (hs : ∀ x, R < |x| → f x = 0) :
    |principalValueOneDim χ hχ f hc hd hf| ≤ 2 * R * K :=
  (abs_principalValueOneDim_le hχ hc hd hf).trans
    (integral_abs_pvQuotient_le hc hd hf hL hR hs)

/-- Uniformity in the finite truncation scale. The constant depends on the cutoff
and on the test function's Lipschitz bound. -/
theorem abs_pvTruncation_le_radius {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {f : ℝ → ℝ} {K : ℝ≥0} {R C : ℝ}
    (hc : Continuous f) (hd : DifferentiableAt ℝ f 0) (hf : HasCompactSupport f)
    (hL : LipschitzWith K f) (hR : 0 ≤ R) (hs : ∀ x, R < |x| → f x = 0)
    (hC : ∀ x, |χ x| ≤ C) (μ : ℝ) :
    |pvTruncation χ μ f| ≤ (1 + C) * (2 * R * K) := by
  have hCn : 0 ≤ C := (abs_nonneg (χ 0)).trans (hC 0)
  rw [hχ.pvTruncation_eq μ hc hf, ← Real.norm_eq_abs]
  have hnorm : ‖∫ u, (1 - χ (μ * u)) * pvQuotient f u‖ ≤
      (1 + C) * ∫ u, |pvQuotient f u| := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le
      ((integrable_pvQuotient hc hd hf).abs.const_mul _) (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right
      ((abs_sub _ _).trans (by simpa using add_le_add_left (hC (μ * u)) 1)) (abs_nonneg _)
  exact hnorm.trans (mul_le_mul_of_nonneg_left
    (integral_abs_pvQuotient_le hc hd hf hL hR hs) (by positivity))

end WaveTurbulence.Resonant
