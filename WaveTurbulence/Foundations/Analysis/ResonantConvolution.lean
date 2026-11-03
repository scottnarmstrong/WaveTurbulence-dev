/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Analysis.CauchyResonance

/-!
# Resonant frequency convolution

The two output centres, `0` and `q`, survive frequency convolution with a
constant independent of the resonance. This is the analytic induction
mechanism for DH21 Lemma 10.2.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Analysis

/-- Translation-invariant form of the quadratic convolution bound. -/
theorem lintegral_shifted_cauchyWeight_mul_le (t q : ℝ) :
    (∫⁻ s : ℝ, ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (cauchyWeight (s - q))) ≤
      ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (cauchyWeight (t - q)) := by
  have heq : (∫⁻ s : ℝ, ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (cauchyWeight (s - q))) =
      ∫⁻ u : ℝ, ENNReal.ofReal (cauchyWeight ((t - q) - u)) * ENNReal.ofReal (cauchyWeight u) := by
    rw [← lintegral_add_right_eq_self
      (fun s : ℝ => ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (cauchyWeight (s - q))) q]
    apply lintegral_congr
    intro u
    rw [show t - (u + q) = (t - q) - u by ring, add_sub_cancel_right]
  rw [heq]
  exact lintegral_cauchyWeight_mul_le (t - q)

/-- The resonance denominator passes through convolution without losing
quadratic decay. Both output centres are necessary. -/
theorem lintegral_resonant_cauchyWeight_le (t q : ℝ) :
    (∫⁻ s : ℝ, ENNReal.ofReal (cauchyWeight (t - s)) *
      ENNReal.ofReal (oscillatoryWeight s) * ENNReal.ofReal (cauchyWeight (s - q))) ≤
      ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal (oscillatoryWeight q) *
        (ENNReal.ofReal (cauchyWeight (t - q)) + ENNReal.ofReal (cauchyWeight t)) := by
  have hJ (s : ℝ) : 0 ≤ oscillatoryWeight s := by unfold oscillatoryWeight; positivity
  have hp (s : ℝ) :
      ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (oscillatoryWeight s) *
          ENNReal.ofReal (cauchyWeight (s - q)) ≤
        ENNReal.ofReal (2 * oscillatoryWeight q) *
          (ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (cauchyWeight (s - q)) +
            ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (cauchyWeight s)) := by
    have hh := ENNReal.ofReal_le_ofReal (oscillatoryWeight_mul_cauchyWeight_le q s)
    rw [ENNReal.ofReal_mul (hJ s), ENNReal.ofReal_mul (mul_nonneg (by norm_num) (hJ q)),
      ENNReal.ofReal_add (cauchyWeight_pos (s - q)).le (cauchyWeight_pos s).le] at hh
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ ENNReal.ofReal (cauchyWeight (t - s)) by positivity)
    convert hm using 1 <;> ring
  have hm1 : Measurable (fun s : ℝ => ENNReal.ofReal (cauchyWeight (t - s)) *
      ENNReal.ofReal (cauchyWeight (s - q))) := by unfold cauchyWeight; fun_prop
  have hm2 : Measurable (fun s : ℝ => ENNReal.ofReal (cauchyWeight (t - s)) *
      ENNReal.ofReal (cauchyWeight s)) := by unfold cauchyWeight; fun_prop
  have hsum : Measurable (fun s : ℝ =>
      ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (cauchyWeight (s - q)) +
      ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (cauchyWeight s)) := by fun_prop
  calc
    _ ≤ ∫⁻ s : ℝ, ENNReal.ofReal (2 * oscillatoryWeight q) *
        (ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (cauchyWeight (s - q)) +
          ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (cauchyWeight s)) := lintegral_mono hp
    _ = ENNReal.ofReal (2 * oscillatoryWeight q) *
        ((∫⁻ s : ℝ, ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (cauchyWeight (s - q))) +
          ∫⁻ s : ℝ, ENNReal.ofReal (cauchyWeight (t - s)) * ENNReal.ofReal (cauchyWeight s)) := by
      rw [lintegral_const_mul _ hsum, lintegral_add_left hm1]
    _ ≤ ENNReal.ofReal (2 * oscillatoryWeight q) *
        (ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (cauchyWeight (t - q)) +
          ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (cauchyWeight t)) :=
      mul_le_mul_of_nonneg_left (add_le_add (lintegral_shifted_cauchyWeight_mul_le t q)
        (lintegral_cauchyWeight_mul_le t)) (by positivity)
    _ = _ := by
      have hc : ENNReal.ofReal (2 * oscillatoryWeight q) * ENNReal.ofReal (4 * Real.pi) =
          ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal (oscillatoryWeight q) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (hJ q)),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      calc
        _ = (ENNReal.ofReal (2 * oscillatoryWeight q) * ENNReal.ofReal (4 * Real.pi)) *
            (ENNReal.ofReal (cauchyWeight (t - q)) + ENNReal.ofReal (cauchyWeight t)) := by ring
        _ = _ := by rw [hc]


end WaveTurbulence.Analysis
