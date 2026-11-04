/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SmallPairStrip

/-!
# The small-region incoherence strip majorant

Different unit interval labels place the outer time within a strip of
radius `2h+|s|/c`. Its mass is bounded by the same fixed first moment,
with gain `4h+2/c`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- Ordinary and first moments are both bounded by the fixed first-moment kernel mass. -/
theorem pair_kernel_moments_le (d : ℕ) (hd : 3 ≤ d) :
    (∫⁻ s : ℝ, ENNReal.ofReal (1/scalarBracket s^d)) ≤
      ENNReal.ofReal (∫ s : ℝ, (1+|s|)/scalarBracket s^d) ∧
    (∫⁻ s : ℝ, ENNReal.ofReal |s| * ENNReal.ofReal (1/scalarBracket s^d)) ≤
      ENNReal.ofReal (∫ s : ℝ, (1+|s|)/scalarBracket s^d) := by
  have hn (s : ℝ) : 0 ≤ (1+|s|)/scalarBracket s^d :=
    div_nonneg (by positivity) (pow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _)
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_first_moment_kernel hd) (ae_of_all _ hn)]
  constructor
  · apply lintegral_mono
    intro s
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right (by linarith [abs_nonneg s])
      (pow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _)
  · apply lintegral_mono
    intro s
    dsimp only
    rw [← ENNReal.ofReal_mul (abs_nonneg s)]
    apply ENNReal.ofReal_le_ofReal
    exact (show |s| * (1/scalarBracket s^d) = |s|/scalarBracket s^d by ring).le.trans
      (div_le_div_of_nonneg_right (by linarith)
        (pow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _))

/-- The incoherence strip retains the small cell-width and inverse-time-scale gains. -/
theorem small_pair_incoherence_strip_le (d : ℕ) (hd : 3 ≤ d)
    {c h : ℝ} (hc : 0 < c) (hh : 0 ≤ h) (e : ℝ) :
    (∫⁻ t : ℝ, ∫⁻ s : ℝ, if |t-e| ≤ 2*h+|s|/c then
      ENNReal.ofReal (1/scalarBracket s^d) else 0) ≤
        ENNReal.ofReal (4*h+2/c) * ENNReal.ofReal (∫ s : ℝ, (1+|s|)/scalarBracket s^d) := by
  have hf : Measurable (fun s : ℝ => ENNReal.ofReal (1/scalarBracket s^d)) := by
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    have hk : Continuous scalarBracket := by unfold scalarBracket; fun_prop
    exact continuous_const.div (hk.pow d) (fun s =>
      pow_ne_zero d (zero_lt_one.trans_le (one_le_scalarBracket s)).ne')
  rw [lintegral_offset_first_moment_strip _ hf hc (mul_nonneg (by norm_num) hh) e]
  obtain ⟨h0,h1⟩ := pair_kernel_moments_le d hd
  refine (add_le_add (mul_le_mul' le_rfl h0) (mul_le_mul' le_rfl h1)).trans_eq ?_
  rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hh))
    (div_nonneg (by norm_num) hc.le)]
  congr 2
  ring

end WaveTurbulence.Sumint
