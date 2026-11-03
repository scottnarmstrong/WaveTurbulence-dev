/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CutoffKernelL1

/-!
# The spectral cutoff time-integration operator

The operator is the actual Bochner integral of the Fourier kernel against
the input density. Joint integrability justifies the spectral Fubini step.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Analysis

/-- Apply the cutoff time kernel to an integrable spectral density. -/
@[expose] noncomputable def cutoffSpectralOperator (χ : ℝ → ℂ) (a : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ q : ℝ, cutoffTimeKernel χ a t q * g q

private theorem kernelProduct_aestronglyMeasurable {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (a : ℝ) {g : ℝ → ℂ} (hg : Integrable g) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => cutoffTimeKernel χ a p.1 p.2 * g p.2)
      (volume.prod volume) :=
  (measurable_cutoffTimeKernel hχ hs a).aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd

/-- Joint integrability of the kernel against an integrable input density. -/
theorem integrable_kernelProduct {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) {a : ℝ} (ha : a ∈ Set.Icc 0 1) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ => cutoffTimeKernel χ a p.1 p.2 * g p.2) (volume.prod volume) := by
  have hm := kernelProduct_aestronglyMeasurable hχ hs a hg
  apply (integrable_prod_iff' hm).mpr
  refine ⟨Filter.Eventually.of_forall (fun q => (integrable_cutoffTimeKernel hχ hs ha q).mul_const (g q)), ?_⟩
  have hb := hg.norm.const_mul (2 * Real.pi * cutoffKernelConstant χ)
  apply hb.mono' hm.prod_swap.norm.integral_prod_right'
  filter_upwards with q
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  simp_rw [norm_mul]
  change (∫ v : ℝ, ‖cutoffTimeKernel χ a v q‖ * ‖g q‖) ≤ _
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (integral_norm_cutoffTimeKernel_le hχ hs ha q) (norm_nonneg _)

/-- The output is an integrable spectral density. -/
theorem integrable_cutoffSpectralOperator {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) {a : ℝ} (ha : a ∈ Set.Icc 0 1) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (cutoffSpectralOperator χ a g) :=
  (integrable_kernelProduct hχ hs ha hg).integral_prod_left

/-- Each defining inner integral is integrable, at every output frequency. -/
theorem integrable_cutoffSpectralOperator_integrand {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) {a : ℝ} (ha : a ∈ Set.Icc 0 1) {g : ℝ → ℂ} (hg : Integrable g)
    (t : ℝ) : Integrable (fun q : ℝ => cutoffTimeKernel χ a t q * g q) := by
  have hm : AEStronglyMeasurable (fun q : ℝ => cutoffTimeKernel χ a t q * g q) :=
    ((measurable_cutoffTimeKernel hχ hs a).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable.mul
      hg.aestronglyMeasurable
  apply (hg.norm.const_mul (2 * cutoffKernelConstant χ)).mono' hm
  filter_upwards with q
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_cutoffTimeKernel_le_uniform hχ hs ha t q) (norm_nonneg _)

/-- Synthesis of the output equals the integral of the synthesized kernels.
This is the first Fubini step for cutoff time integration. -/
theorem spectralSynthesis_cutoffSpectralOperator {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) {a : ℝ} (ha : a ∈ Set.Icc 0 1) {g : ℝ → ℂ} (hg : Integrable g)
    (t : ℝ) : spectralSynthesis (cutoffSpectralOperator χ a g) t =
      ∫ q : ℝ, cutoffPrimitive χ a q t * g q := by
  have hj := integrable_kernelProduct hχ hs ha hg
  have hm := kernelProduct_aestronglyMeasurable hχ hs a hg
  have hφ : AEStronglyMeasurable (fun p : ℝ × ℝ => timePhase t p.1 *
      (cutoffTimeKernel χ a p.1 p.2 * g p.2)) (volume.prod volume) :=
    ((contDiff_timePhase t).continuous.measurable.comp measurable_fst).aestronglyMeasurable.mul hm
  have hjφ : Integrable (fun p : ℝ × ℝ => timePhase t p.1 *
      (cutoffTimeKernel χ a p.1 p.2 * g p.2)) (volume.prod volume) := by
    apply hj.norm.mono' hφ
    filter_upwards with p
    rw [norm_mul, norm_timePhase, one_mul]
  rw [spectralSynthesis_eq_integral]
  calc
    _ = ∫ v : ℝ, ∫ q : ℝ, timePhase t v * (cutoffTimeKernel χ a v q * g q) := by
      apply integral_congr_ae
      filter_upwards with v
      exact (integral_const_mul _ _).symm
    _ = ∫ q : ℝ, ∫ v : ℝ, timePhase t v * (cutoffTimeKernel χ a v q * g q) :=
      integral_integral_swap hjφ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with q
      simp_rw [← mul_assoc]
      rw [integral_mul_const, ← spectralSynthesis_eq_integral,
        spectralSynthesis_cutoffTimeKernel hχ hs ha]

end WaveTurbulence.Analysis
