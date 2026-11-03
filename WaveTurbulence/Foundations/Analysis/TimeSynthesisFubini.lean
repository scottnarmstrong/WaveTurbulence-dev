/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CutoffSpectralOperator

/-!
# Time integration of an integrable spectral representation

Fubini converts time integration into multiplication by the oscillatory
primitive. The result includes both endpoint orders.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace WaveTurbulence.Analysis

private theorem continuous_timePhase_uncurry : Continuous (fun p : ℝ × ℝ => timePhase p.1 p.2) := by
  have hr : Continuous (fun p : ℝ × ℝ => 2 * Real.pi * p.1 * p.2) := by fun_prop
  exact Complex.continuous_exp.comp ((Complex.ofRealCLM.continuous.comp hr).mul continuous_const)

private theorem timePhase_swap (q t : ℝ) : timePhase q t = timePhase t q := by
  unfold timePhase
  congr 1
  push_cast
  ring

private theorem integral_timePrimitive_mul_of_le {g : ℝ → ℂ} (hg : Integrable g)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ q : ℝ, timePrimitive a q b * g q) = ∫ s in a..b, spectralSynthesis g s := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => timePhase p.1 p.2 * g p.1)
      (volume.prod (volume.restrict (Icc a b))) :=
    continuous_timePhase_uncurry.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_fst
  have hi : Integrable (fun p : ℝ × ℝ => timePhase p.1 p.2 * g p.1)
      (volume.prod (volume.restrict (Icc a b))) := by
    apply (hg.norm.comp_fst (volume.restrict (Icc a b))).mono' hm
    filter_upwards with p
    rw [norm_mul, norm_timePhase, one_mul]
  calc
    (∫ q : ℝ, timePrimitive a q b * g q) =
        ∫ q : ℝ, ∫ s in Icc a b, timePhase q s * g q := by
      apply integral_congr_ae
      filter_upwards with q
      rw [timePrimitive, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
        integral_mul_const]
    _ = ∫ s in Icc a b, ∫ q : ℝ, timePhase q s * g q := integral_integral_swap hi
    _ = ∫ s in Icc a b, spectralSynthesis g s := by
      apply integral_congr_ae
      filter_upwards with s
      rw [spectralSynthesis_eq_integral]
      apply integral_congr_ae
      filter_upwards with q
      rw [timePhase_swap q s]
    _ = _ := by rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- Integrate an integrable spectral representation over any oriented
interval. -/
theorem integral_timePrimitive_mul {g : ℝ → ℂ} (hg : Integrable g) (a b : ℝ) :
    (∫ q : ℝ, timePrimitive a q b * g q) = ∫ s in a..b, spectralSynthesis g s := by
  rcases le_total a b with hab | hba
  · exact integral_timePrimitive_mul_of_le hg hab
  · calc
      _ = ∫ q : ℝ, -(timePrimitive b q a * g q) := by
        apply integral_congr_ae
        filter_upwards with q
        rw [timePrimitive, intervalIntegral.integral_symm]
        simp only [timePrimitive, neg_mul]
      _ = -(∫ q : ℝ, timePrimitive b q a * g q) := integral_neg _
      _ = -(∫ s in b..a, spectralSynthesis g s) := by rw [integral_timePrimitive_mul_of_le hg hba]
      _ = _ := (intervalIntegral.integral_symm b a).symm

/-- Synthesis intertwines the spectral kernel operator with the actual
cutoff time integral. -/
theorem spectralSynthesis_cutoffSpectralOperator_eq_integral {χ : ℝ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ) {a : ℝ} (ha : a ∈ Icc 0 1)
    {g : ℝ → ℂ} (hg : Integrable g) (t : ℝ) :
    spectralSynthesis (cutoffSpectralOperator χ a g) t =
      χ t * ∫ s in a..t, spectralSynthesis g s := by
  rw [spectralSynthesis_cutoffSpectralOperator hχ hs ha hg]
  simp only [cutoffPrimitive]
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_timePrimitive_mul hg]

end WaveTurbulence.Analysis
