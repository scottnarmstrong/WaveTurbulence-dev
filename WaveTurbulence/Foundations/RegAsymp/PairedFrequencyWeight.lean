/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.PairedProfile
public import WaveTurbulence.Foundations.RegAsymp.TemporalSplitEnvelope

/-! # The actual source frequency controls the local time Fourier weight -/

public section
namespace WaveTurbulence.RegAsymp
open WaveTurbulence.Fourier ClassJR

/-- The ordinary Fourier frequency is λ/2 and its maximum bracket is
bounded by the literal source weight base1+|λ1|+|λ2|. -/
theorem timeBracket_pairedTimeFrequency_le (lam : ℝ × ℝ) :
    timeBracket (pairedTimeFrequency lam) ≤ 1+|lam.1|+|lam.2| := by
  have hs (x : ℝ) : Real.sqrt (1+(x/2)^2) ≤ 1+|x| := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_abs x,abs_nonneg x]
  unfold timeBracket
  apply Finset.sup'_le
  intro j _
  cases j with
  | none => change (1:ℝ) ≤ _; linarith [abs_nonneg lam.1,abs_nonneg lam.2]
  | some i =>
    fin_cases i
    · change Real.sqrt (1+(lam.1/2)^2) ≤ 1+|lam.1|+|lam.2|
      exact (hs lam.1).trans (le_add_of_nonneg_right (abs_nonneg lam.2))
    · change Real.sqrt (1+(lam.2/2)^2) ≤ 1+|lam.1|+|lam.2|
      exact (hs lam.2).trans (by linarith [abs_nonneg lam.1])


/-- No extra frequency power is needed when passing from source λ to
ordinary time Fourier variables. -/
theorem timeWeight_pairedTimeFrequency_le {η : ℝ} (hη : 0 ≤ η) (lam : ℝ × ℝ) :
    timeWeight η (pairedTimeFrequency lam) ≤ wL η lam := by
  rw [timeWeight,wL_eq_ofReal_frequency_weight]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
    (timeBracket_pos (pairedTimeFrequency lam)).le (timeBracket_pairedTimeFrequency_le lam) hη)

end WaveTurbulence.RegAsymp
