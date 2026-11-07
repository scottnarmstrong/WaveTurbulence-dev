/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceFrequencyShear
public import WaveTurbulence.Foundations.Fourier.TimeWeights

/-!
# Uniform Japanese bracket cost of the source frequency shear

The elementary bound uses the absolute factor four. It is independent
of all source parameters and is sufficient after interpolation.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.SumintPar

private theorem sqrt_one_add_sq_le (x : ℝ) : Real.sqrt (1+x^2) ≤ 1+|x| := by
  have hs := Real.sq_sqrt (show 0 ≤ 1+x^2 by positivity)
  have hn := Real.sqrt_nonneg (1+x^2)
  have ha := abs_nonneg x
  have he := sq_abs x
  nlinarith

private theorem abs_le_timeBracket (ξ : Fin 3 → ℝ) (j : Fin 3) :
    |ξ j| ≤ Fourier.timeBracket ξ := by
  apply le_trans _ (Fourier.bracket_le_timeBracket ξ j)
  have hs := Real.sq_sqrt (show 0 ≤ 1+(ξ j)^2 by positivity)
  have hn := Real.sqrt_nonneg (1+(ξ j)^2)
  have he := sq_abs (ξ j)
  nlinarith [abs_nonneg (ξ j)]

/-- The inverse frequency shear has an absolute bracket distortion at most four. -/
theorem timeBracket_sourceFrequencyUnshear_le (ξ : Fin 3 → ℝ) :
    Fourier.timeBracket (sourceFrequencyUnshear ξ) ≤ 4*Fourier.timeBracket ξ := by
  have h1 := Fourier.one_le_timeBracket ξ
  apply Fourier.timeBracket_le (by linarith)
  intro j
  fin_cases j
  · change Real.sqrt (1+(ξ 0-ξ 1-ξ 2)^2) ≤ _
    have ha : |ξ 0-ξ 1-ξ 2| ≤ |ξ 0|+|ξ 1|+|ξ 2| := by
      exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    exact (sqrt_one_add_sq_le _).trans (by
      linarith [abs_le_timeBracket ξ 0,abs_le_timeBracket ξ 1,abs_le_timeBracket ξ 2])
  · change Real.sqrt (1+(ξ 1)^2) ≤ _
    linarith [Fourier.bracket_le_timeBracket ξ 1]
  · change Real.sqrt (1+(ξ 2)^2) ≤ _
    linarith [Fourier.bracket_le_timeBracket ξ 2]

/-- The positive regularity weight costs only the absolute scalar four to that power. -/
theorem timeWeight_sourceShear_le {θ : ℝ} (hθ : 0 ≤ θ) (ξ : Fin 3 → ℝ) :
    Fourier.timeWeight θ ξ ≤ ENNReal.ofReal (4^θ)*
      Fourier.timeWeight θ (sourceFrequencyShear ξ) := by
  have hb := timeBracket_sourceFrequencyUnshear_le (sourceFrequencyShear ξ)
  rw [sourceFrequencyUnshear_shear] at hb
  unfold Fourier.timeWeight
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
    ← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (Fourier.timeBracket_pos _).le]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (Fourier.timeBracket_pos ξ).le hb hθ)

end WaveTurbulence.SumintPar
