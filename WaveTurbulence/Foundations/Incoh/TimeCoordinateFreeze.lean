/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeWeights

/-!
# Frequency algebra for freezing a time coordinate

Fixing one clock removes the corresponding output frequency; the remaining
frequency weight never increases at nonnegative regularity.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Delete the frequency in the clock that is fixed. -/
@[expose] def eraseTimeFrequency {r : ℕ} (j : Fin r) (ξ : Fin r → ℝ) : Fin r → ℝ :=
  Function.update ξ j 0

theorem timeBracket_eraseTimeFrequency_le {r : ℕ} (j : Fin r) (ξ : Fin r → ℝ) :
    Fourier.timeBracket (eraseTimeFrequency j ξ) ≤ Fourier.timeBracket ξ := by
  apply Fourier.timeBracket_le (Fourier.one_le_timeBracket ξ)
  intro i
  by_cases hi : i = j
  · subst i
    simpa only [eraseTimeFrequency, Function.update_self, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero, Real.sqrt_one] using Fourier.one_le_timeBracket ξ
  · simpa only [eraseTimeFrequency, Function.update_of_ne hi] using Fourier.bracket_le_timeBracket ξ i

theorem timeWeight_eraseTimeFrequency_le {r : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    (j : Fin r) (ξ : Fin r → ℝ) :
    Fourier.timeWeight θ (eraseTimeFrequency j ξ) ≤ Fourier.timeWeight θ ξ :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (Fourier.timeBracket_pos _).le
    (timeBracket_eraseTimeFrequency_le j ξ) hθ)

/-- Fourier pairing splits into the surviving frequencies and the fixed-clock phase. -/
theorem timePairing_update {r : ℕ} (j : Fin r) (ξ t : Fin r → ℝ) (c : ℝ) :
    Fourier.timePairing r ξ (Function.update t j c) =
      Fourier.timePairing r t (eraseTimeFrequency j ξ) + c * ξ j := by
  classical
  change (∑ i, ξ i * Function.update t j c i) = (∑ i, t i * Function.update ξ j 0 i) + c * ξ j
  have he (i : Fin r) : ξ i * Function.update t j c i =
      t i * Function.update ξ j 0 i + if i = j then c * ξ j else 0 := by
    by_cases hi : i = j
    · subst i
      simp only [Function.update_self, ite_true, mul_zero, zero_add, mul_comm]
    · simp only [Function.update_of_ne hi, hi, ite_false, add_zero, mul_comm]
  simp_rw [he, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end WaveTurbulence.Incoh
