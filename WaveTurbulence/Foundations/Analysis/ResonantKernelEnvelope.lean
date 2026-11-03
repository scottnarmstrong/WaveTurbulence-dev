/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.ResonantConvolution

/-!
# The two-centre time-kernel envelope

Passing a quadratic input envelope through the cutoff time kernel produces
the two permitted output centres and one resonance denominator.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Analysis

/-- Integrating a Japanese bracket against a translated Cauchy envelope. -/
theorem lintegral_oscillatoryWeight_cauchyWeight_le (q : ℝ) :
    (∫⁻ s : ℝ, ENNReal.ofReal (oscillatoryWeight s) * ENNReal.ofReal (cauchyWeight (s - q))) ≤
      ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (oscillatoryWeight q) := by
  have hJ (s : ℝ) : 0 ≤ oscillatoryWeight s := by unfold oscillatoryWeight; positivity
  have hp (s : ℝ) : ENNReal.ofReal (oscillatoryWeight s) * ENNReal.ofReal (cauchyWeight (s - q)) ≤
      ENNReal.ofReal (2 * oscillatoryWeight q) *
        (ENNReal.ofReal (cauchyWeight (s - q)) + ENNReal.ofReal (cauchyWeight s)) := by
    have hh := ENNReal.ofReal_le_ofReal (oscillatoryWeight_mul_cauchyWeight_le q s)
    rw [ENNReal.ofReal_mul (hJ s), ENNReal.ofReal_mul (mul_nonneg (by norm_num) (hJ q)),
      ENNReal.ofReal_add (cauchyWeight_pos (s - q)).le (cauchyWeight_pos s).le] at hh
    exact hh
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (cauchyWeight (s - q))) := by
    unfold cauchyWeight
    fun_prop
  have hmsum : Measurable (fun s : ℝ => ENNReal.ofReal (cauchyWeight (s - q)) +
      ENNReal.ofReal (cauchyWeight s)) := by unfold cauchyWeight; fun_prop
  calc
    _ ≤ ∫⁻ s : ℝ, ENNReal.ofReal (2 * oscillatoryWeight q) *
        (ENNReal.ofReal (cauchyWeight (s - q)) + ENNReal.ofReal (cauchyWeight s)) := lintegral_mono hp
    _ = ENNReal.ofReal (2 * oscillatoryWeight q) *
        (ENNReal.ofReal Real.pi + ENNReal.ofReal Real.pi) := by
      rw [lintegral_const_mul _ hmsum, lintegral_add_left hm,
        lintegral_sub_right_eq_self (fun s : ℝ => ENNReal.ofReal (cauchyWeight s)) q,
        lintegral_cauchyWeight]
    _ = _ := by
      rw [← ENNReal.ofReal_add Real.pi_pos.le Real.pi_pos.le,
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (hJ q)),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- A complete time-kernel envelope maps one input centre to the two
output centres `0,q`, gaining `⟨q⟩⁻¹`. -/
theorem lintegral_timeKernel_envelope_le (t q : ℝ) :
    (∫⁻ s : ℝ, ENNReal.ofReal (oscillatoryWeight s) *
      (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - s))) *
        ENNReal.ofReal (cauchyWeight (s - q))) ≤
      ENNReal.ofReal (12 * Real.pi) * ENNReal.ofReal (oscillatoryWeight q) *
        (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - q))) := by
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (cauchyWeight t) *
      (ENNReal.ofReal (oscillatoryWeight s) * ENNReal.ofReal (cauchyWeight (s - q)))) := by
    unfold oscillatoryWeight cauchyWeight
    fun_prop
  have heq (s : ℝ) :
      ENNReal.ofReal (oscillatoryWeight s) *
          (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - s))) *
            ENNReal.ofReal (cauchyWeight (s - q)) =
        ENNReal.ofReal (cauchyWeight t) *
          (ENNReal.ofReal (oscillatoryWeight s) * ENNReal.ofReal (cauchyWeight (s - q))) +
        ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (oscillatoryWeight s) *
          ENNReal.ofReal (cauchyWeight (s - q)) := by ring
  simp_rw [heq]
  rw [lintegral_add_left hm, lintegral_const_mul _ (by
    unfold oscillatoryWeight cauchyWeight; fun_prop)]
  have h1 := mul_le_mul_of_nonneg_left (lintegral_oscillatoryWeight_cauchyWeight_le q)
    (show 0 ≤ ENNReal.ofReal (cauchyWeight t) by positivity)
  have h2 := lintegral_resonant_cauchyWeight_le t q
  have h1' : ENNReal.ofReal (cauchyWeight t) *
      (ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (oscillatoryWeight q)) ≤
      ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (oscillatoryWeight q) *
        (ENNReal.ofReal (cauchyWeight t) + ENNReal.ofReal (cauchyWeight (t - q))) := by
    have hh := mul_le_mul_of_nonneg_left
      (show ENNReal.ofReal (cauchyWeight t) ≤ ENNReal.ofReal (cauchyWeight t) +
        ENNReal.ofReal (cauchyWeight (t - q)) from le_self_add)
      (show 0 ≤ ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (oscillatoryWeight q) by positivity)
    simpa only [mul_comm] using hh
  have hh := add_le_add (h1.trans h1') h2
  have hc : ENNReal.ofReal (4 * Real.pi) + ENNReal.ofReal (8 * Real.pi) = ENNReal.ofReal (12 * Real.pi) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc
    _ ≤ _ := hh
    _ = _ := by rw [← hc]; ring

end WaveTurbulence.Analysis
