/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.TimeSynthesisFubini
public import WaveTurbulence.Foundations.Analysis.ResonantKernelEnvelope

/-!
# Finite frequency envelopes

A finite sum of translated Cauchy weights records the endpoint choices
at all vertices of an oscillatory tree. Coefficients are extended
nonnegative reals so the integral estimates need no auxiliary finiteness
premises; actual spectral densities are separately proved integrable.
-/

public section

open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Analysis

/-- A finite collection of frequency centres and their nonnegative weights. -/
@[expose] noncomputable def frequencyEnvelope {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (w : ι → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∑ i, w i * ENNReal.ofReal (cauchyWeight (t - c i))

theorem measurable_frequencyEnvelope {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (w : ι → ℝ≥0∞) : Measurable (frequencyEnvelope c w) := by
  unfold frequencyEnvelope cauchyWeight
  fun_prop

/-- Total mass of a finite frequency envelope. -/
theorem lintegral_frequencyEnvelope {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (w : ι → ℝ≥0∞) :
    (∫⁻ t : ℝ, frequencyEnvelope c w t) = (∑ i, w i) * ENNReal.ofReal Real.pi := by
  unfold frequencyEnvelope
  rw [lintegral_finsetSum _ (by intro i hi; unfold cauchyWeight; fun_prop)]
  have hm (i : ι) : Measurable (fun t : ℝ => ENNReal.ofReal (cauchyWeight (t - c i))) := by
    unfold cauchyWeight
    fun_prop
  simp_rw [lintegral_const_mul _ (hm _),
    lintegral_sub_right_eq_self (fun t : ℝ => ENNReal.ofReal (cauchyWeight t)), lintegral_cauchyWeight]
  exact (Finset.sum_mul ..).symm

/-- Integrating the full time-kernel envelope against a finite input
packet produces its two endpoint centres and one denominator per centre. -/
theorem lintegral_timeKernel_frequencyEnvelope_le {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (w : ι → ℝ≥0∞) (t : ℝ) :
    (∫⁻ s : ℝ, ENNReal.ofReal (oscillatoryWeight s) *
      (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - s))) *
        frequencyEnvelope c w s) ≤
      ENNReal.ofReal (12 * Real.pi) *
        ∑ i, w i * ENNReal.ofReal (oscillatoryWeight (c i)) *
          (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - c i))) := by
  unfold frequencyEnvelope
  simp_rw [Finset.mul_sum]
  rw [lintegral_finsetSum _ (by intro i hi; unfold oscillatoryWeight cauchyWeight; fun_prop)]
  simp_rw [show ∀ i s, ENNReal.ofReal (oscillatoryWeight s) *
      (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - s))) *
        (w i * ENNReal.ofReal (cauchyWeight (s - c i))) =
      w i * (ENNReal.ofReal (oscillatoryWeight s) *
        (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - s))) *
          ENNReal.ofReal (cauchyWeight (s - c i))) by intros; ring]
  have hm (i : ι) : Measurable (fun s : ℝ => ENNReal.ofReal (oscillatoryWeight s) *
      (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - s))) *
        ENNReal.ofReal (cauchyWeight (s - c i))) := by
    unfold oscillatoryWeight cauchyWeight
    fun_prop
  simp_rw [lintegral_const_mul _ (hm _)]
  calc
    _ ≤ ∑ i, w i * (ENNReal.ofReal (12 * Real.pi) * ENNReal.ofReal (oscillatoryWeight (c i)) *
        (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - c i)))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul' le_rfl (lintegral_timeKernel_envelope_le t (c i))
    _ = _ := by apply Finset.sum_congr rfl; intros; ring

/-- The actual cutoff spectral operator obeys the finite packet bound. -/
theorem enorm_cutoffSpectralOperator_le_frequencyEnvelope {ι : Type*} [Fintype ι]
    {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ)
    {a : ℝ} (ha : a ∈ Set.Icc 0 1) {g : ℝ → ℂ}
    (c : ι → ℝ) (w : ι → ℝ≥0∞) (hg : ∀ s, ‖g s‖ₑ ≤ frequencyEnvelope c w s) (t : ℝ) :
    ‖cutoffSpectralOperator χ a g t‖ₑ ≤
      ENNReal.ofReal (cutoffKernelConstant χ) * ENNReal.ofReal (12 * Real.pi) *
        ∑ i, w i * ENNReal.ofReal (oscillatoryWeight (c i)) *
          (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - c i))) := by
  have hk (s : ℝ) : ‖cutoffTimeKernel χ a t s‖ₑ ≤
      ENNReal.ofReal (cutoffKernelConstant χ) * ENNReal.ofReal (oscillatoryWeight s) *
        (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - s))) := by
    have hh := ENNReal.ofReal_le_ofReal (norm_cutoffTimeKernel_le hχ hs ha t s)
    simpa only [ofReal_norm, ENNReal.ofReal_mul (cutoffKernelConstant_nonneg χ),
      ENNReal.ofReal_mul (mul_nonneg (cutoffKernelConstant_nonneg χ) (oscillatoryWeight_pos s).le),
      ENNReal.ofReal_add (cauchyWeight_pos t).le (cauchyWeight_pos (t - s)).le] using hh
  calc
    _ ≤ ∫⁻ s : ℝ, ‖cutoffTimeKernel χ a t s * g s‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ s : ℝ, ENNReal.ofReal (cutoffKernelConstant χ) *
        (ENNReal.ofReal (oscillatoryWeight s) *
          (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - s))) *
            frequencyEnvelope c w s) := by
      apply lintegral_mono
      intro s
      dsimp only
      rw [enorm_mul]
      convert mul_le_mul' (hk s) (hg s) using 1; ring
    _ = ENNReal.ofReal (cutoffKernelConstant χ) *
        ∫⁻ s : ℝ, ENNReal.ofReal (oscillatoryWeight s) *
          (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - s))) *
            frequencyEnvelope c w s := by
      rw [lintegral_const_mul _ (by
        apply Measurable.mul _ (measurable_frequencyEnvelope c w)
        unfold oscillatoryWeight cauchyWeight
        fun_prop)]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul'
        (le_refl (ENNReal.ofReal (cutoffKernelConstant χ)))
        (lintegral_timeKernel_frequencyEnvelope_le c w t)

end WaveTurbulence.Analysis
