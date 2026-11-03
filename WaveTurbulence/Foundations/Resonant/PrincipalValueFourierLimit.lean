/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.PrincipalValueFourier
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

namespace WaveTurbulence.Resonant

/-- Exact remainder-plus-central-term decomposition. -/
theorem pvFourierTruncation_eq {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {f : ℝ → ℂ} {K : ℝ≥0} (hf : Integrable f) (hL : LipschitzWith K f) (μ η : ℝ) :
    pvTruncationComplex χ μ (fun u => f u * unitPhase η u) =
      (∫ u : ℝ, ((1 - χ (μ * u) : ℝ) : ℂ) * pvRemainder f u * unitPhase η u) +
        f 0 * ∫ t in (-1 : ℝ)..1,
          (((1 - χ (μ * t)) / t : ℝ) : ℂ) * unitPhase η t := by
  obtain ⟨C, hCb⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  have hC : ∀ t, |χ t| ≤ C := by simpa only [Real.norm_eq_abs] using hCb
  let q : ℝ → ℝ := fun u => (1 - χ (μ * u)) / u
  let z : ℝ → ℂ := fun u => (q u : ℂ) * unitPhase η u
  let c : ℝ → ℂ := (Icc (-1 : ℝ) 1).indicator z
  let r : ℝ → ℂ := fun u => ((1 - χ (μ * u) : ℝ) : ℂ) *
    pvRemainder f u * unitPhase η u
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
  unfold pvTruncationComplex
  change (∫ u, (q u : ℂ) * (f u * unitPhase η u)) =
    (∫ u, r u) + f 0 * ∫ t in (-1 : ℝ)..1, z t
  rw [heq, integral_add hir (hic.const_mul (f 0)), integral_const_mul, hcval]

/-- Existence for integrable Lipschitz amplitudes. No derivative at the origin
is needed, since cancellation gives an integrable remainder. -/
theorem tendsto_pvFourierTruncation_of_lipschitz {χ : ℝ → ℝ} (hχ : IsPVCutoff χ)
    {f : ℝ → ℂ} {K : ℝ≥0} (hf : Integrable f) (hL : LipschitzWith K f) (η : ℝ) :
    Tendsto (fun μ => pvTruncationComplex χ μ (fun u => f u * unitPhase η u)) atTop
      (𝓝 ((∫ u : ℝ, pvRemainder f u * unitPhase η u) +
        f 0 * (2 * Complex.I * (∫ t in (0 : ℝ)..1, η * Real.sinc (η * t) : ℝ)))) := by
  obtain ⟨C, hCb⟩ := hχ.cont.bounded_above_of_compact_support hχ.compact
  have hC : ∀ t, |χ t| ≤ C := by simpa only [Real.norm_eq_abs] using hCb
  have hCn : 0 ≤ C := (abs_nonneg (χ 0)).trans (hC 0)
  have hi := integrable_pvRemainder hf hL
  have hr : Tendsto (fun μ : ℝ => ∫ u : ℝ,
      ((1 - χ (μ * u) : ℝ) : ℂ) * pvRemainder f u * unitPhase η u) atTop
      (𝓝 (∫ u : ℝ, pvRemainder f u * unitPhase η u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => (1 + C) * ‖pvRemainder f u‖) ?_ ?_ (hi.norm.const_mul _) ?_
    · refine Eventually.of_forall fun μ => ?_
      exact ((Complex.continuous_ofReal.comp
        (continuous_const.sub (hχ.cont.comp (continuous_const.mul continuous_id)))).aestronglyMeasurable.mul
          hi.aestronglyMeasurable).mul (continuous_unitPhase η).aestronglyMeasurable
    · refine Eventually.of_forall fun μ => Eventually.of_forall fun u => ?_
      rw [norm_mul, norm_mul, norm_unitPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        ((abs_sub _ _).trans (by simpa using add_le_add_left (hC (μ * u)) 1)) (norm_nonneg _)
    · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
      have hne : u ≠ 0 := by simpa using hu
      apply tendsto_const_nhds.congr'
      filter_upwards [hχ.eventually_comp_eq_zero hne] with μ hμ
      simp only [hμ, sub_zero, Complex.ofReal_one, one_mul]
  have hcenter : Tendsto (fun μ : ℝ => ∫ t in (0 : ℝ)..1,
      (1 - χ (μ * t)) * (η * Real.sinc (η * t))) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, η * Real.sinc (η * t))) := by
    simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hib : Integrable (fun _ : ℝ => (1 + C) * |η|)
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 + C) * |η|) volume 0 1).1
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 + C) * |η|)
      ?_ ?_ hib ?_
    · exact Eventually.of_forall fun μ =>
        ((continuous_const.sub (hχ.cont.comp (continuous_const.mul continuous_id))).mul
          (continuous_const.mul (Real.continuous_sinc.comp
            (continuous_const.mul continuous_id)))).aestronglyMeasurable
    · refine Eventually.of_forall fun μ => Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul
        ((abs_sub _ _).trans (by simpa using add_le_add_left (hC (μ * t)) 1))
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sinc_le_one _))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      apply tendsto_const_nhds.congr'
      filter_upwards [hχ.eventually_comp_eq_zero ht.1.ne'] with μ hμ
      simp only [hμ, sub_zero, one_mul]
  have hc : Tendsto (fun μ : ℝ => ∫ t in (-1 : ℝ)..1,
      (((1 - χ (μ * t)) / t : ℝ) : ℂ) * unitPhase η t) atTop
      (𝓝 (2 * Complex.I * (∫ t in (0 : ℝ)..1, η * Real.sinc (η * t) : ℝ))) := by
    have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp hcenter).const_mul (2 * Complex.I)
    exact hh.congr fun μ => (integral_centralFourier_eq hχ μ η).symm
  exact (hr.add (hc.const_mul (f 0))).congr fun μ =>
    (pvFourierTruncation_eq hχ hf hL μ η).symm

end WaveTurbulence.Resonant
