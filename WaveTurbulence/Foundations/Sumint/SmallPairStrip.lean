/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.StripMoments
public import WaveTurbulence.Foundations.Sumint.BilinearSmallIntegral

/-!
# Integrated stationary-phase majorants on the bad-pair strips

The entire-line first-moment kernel is integrable for dimension at least
three. Its strip integral has an additional reciprocal time scale.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- The ordering-strip majorant is controlled by the integrable first moment. -/
theorem small_pair_ordering_strip_le (d : ℕ) (hd : 3 ≤ d) {c : ℝ} (hc : 0 < c) (e : ℝ) :
    (∫⁻ t : ℝ, ∫⁻ s : ℝ, if |t-e| ≤ |s|/c then
      ENNReal.ofReal (1/scalarBracket s^d) else 0) ≤
        ENNReal.ofReal (2/c) * ENNReal.ofReal (∫ s : ℝ, (1+|s|)/scalarBracket s^d) := by
  have hf : Measurable (fun s : ℝ => ENNReal.ofReal (1/scalarBracket s^d)) := by
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    have hk : Continuous scalarBracket := by unfold scalarBracket; fun_prop
    exact continuous_const.div (hk.pow d) (fun s =>
      pow_ne_zero d (zero_lt_one.trans_le (one_le_scalarBracket s)).ne')
  rw [lintegral_first_moment_strip _ hf hc e]
  apply mul_le_mul_right
  have hn (s : ℝ) : 0 ≤ (1+|s|)/scalarBracket s^d :=
    div_nonneg (by positivity) (pow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _)
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_first_moment_kernel hd) (ae_of_all _ hn)]
  apply lintegral_mono
  intro s
  dsimp only
  rw [← ENNReal.ofReal_mul (abs_nonneg s)]
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 < scalarBracket s^d := pow_pos (zero_lt_one.trans_le (one_le_scalarBracket _)) _
  exact (show |s| * (1/scalarBracket s^d) = |s|/scalarBracket s^d by ring).le.trans
    (div_le_div_of_nonneg_right (by linarith) hp.le)

end WaveTurbulence.Sumint
