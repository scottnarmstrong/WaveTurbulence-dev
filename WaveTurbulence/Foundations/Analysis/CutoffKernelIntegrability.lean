/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CutoffTimeKernelBound
public import WaveTurbulence.Foundations.Analysis.SpectralSynthesis

/-!
# Measurability and integrability of the cutoff time kernel

These facts justify the spectral Fubini steps in the tree induction.
-/

public section

open MeasureTheory
open scoped ContDiff FourierTransform

namespace WaveTurbulence.Analysis

private theorem timePhase_comm (q t : ℝ) : timePhase q t = timePhase t q := by
  unfold timePhase
  congr 1
  push_cast
  ring

/-- Joint measurability of the cutoff time kernel in its two frequencies. -/
theorem measurable_cutoffTimeKernel {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) (a : ℝ) :
    Measurable (fun p : ℝ × ℝ => cutoffTimeKernel χ a p.1 p.2) := by
  have hi := hχ.continuous.integrable_of_hasCompactSupport (μ := volume) hs
  have hFT := (continuous_fourier_of_integrable hi).measurable
  have hi0 := (contDiff_cutoffPrimitive hχ a 0).continuous.integrable_of_hasCompactSupport
    (μ := volume) (hasCompactSupport_cutoffPrimitive hs a 0)
  have hm0 : Measurable (fun p : ℝ × ℝ => cutoffTimeKernel χ a p.1 0) :=
    (continuous_fourier_of_integrable hi0).measurable.comp measurable_fst
  have hmphase : Measurable (fun q : ℝ => timePhase q a) := by
    have heq : (fun q : ℝ => timePhase q a) = timePhase a := funext (fun q => timePhase_comm q a)
    rw [heq]
    exact (contDiff_timePhase a).continuous.measurable
  have hmden : Measurable (fun q : ℝ => (2 * Real.pi * q : ℂ) * Complex.I) := by
    convert ((Complex.ofRealCLM.continuous.measurable.const_mul (2 * Real.pi : ℂ)).mul_const Complex.I) using 1
    ext q
    simp only [Complex.ofRealCLM_apply]
  have hmf : Measurable (fun p : ℝ × ℝ =>
      (𝓕 χ (p.1 - p.2) - timePhase p.2 a * 𝓕 χ p.1) /
        ((2 * Real.pi * p.2 : ℂ) * Complex.I)) := by
    exact ((hFT.comp (measurable_fst.sub measurable_snd)).sub
      ((hmphase.comp measurable_snd).mul (hFT.comp measurable_fst))).div (hmden.comp measurable_snd)
  have heq : (fun p : ℝ × ℝ => cutoffTimeKernel χ a p.1 p.2) =
      (fun p : ℝ × ℝ => if p.2 = 0 then cutoffTimeKernel χ a p.1 0 else
        (𝓕 χ (p.1 - p.2) - timePhase p.2 a * 𝓕 χ p.1) /
          ((2 * Real.pi * p.2 : ℂ) * Complex.I)) := by
    funext p
    by_cases h : p.2 = 0
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte, cutoffTimeKernel_eq_of_ne_zero hi a p.1 p.2 h]
  rw [heq]
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) hm0 hmf

/-- Integrability in the output frequency. -/
theorem integrable_cutoffTimeKernel {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) {a : ℝ} (ha : a ∈ Set.Icc 0 1) (q : ℝ) :
    Integrable (fun t : ℝ => cutoffTimeKernel χ a t q) := by
  have hi := (contDiff_cutoffPrimitive hχ a q).continuous.integrable_of_hasCompactSupport
    (μ := volume) (hasCompactSupport_cutoffPrimitive hs a q)
  have hm := (continuous_fourier_of_integrable hi).aestronglyMeasurable (μ := volume)
  have hw : Integrable cauchyWeight := integrable_inv_one_add_sq
  have hb : Integrable (fun t : ℝ => cutoffKernelConstant χ * oscillatoryWeight q *
      (cauchyWeight t + cauchyWeight (t - q))) :=
    (hw.add (hw.comp_sub_right q)).const_mul _
  exact hb.mono' hm (Filter.Eventually.of_forall fun t => norm_cutoffTimeKernel_le hχ hs ha t q)

/-- Fourier inversion for the kernel, in the synthesized representation. -/
theorem spectralSynthesis_cutoffTimeKernel {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hs : HasCompactSupport χ) {a : ℝ} (ha : a ∈ Set.Icc 0 1) (q t : ℝ) :
    spectralSynthesis (fun v => cutoffTimeKernel χ a v q) t = cutoffPrimitive χ a q t := by
  have hi := (contDiff_cutoffPrimitive hχ a q).continuous.integrable_of_hasCompactSupport
    (μ := volume) (hasCompactSupport_cutoffPrimitive hs a q)
  exact hi.fourierInv_fourier_eq (integrable_cutoffTimeKernel hχ hs ha q)
    (contDiff_cutoffPrimitive hχ a q).continuous.continuousAt

end WaveTurbulence.Analysis
