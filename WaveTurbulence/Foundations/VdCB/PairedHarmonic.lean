/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.NumberTheory.SawtoothFourier

/-!
# Symmetric harmonic cancellation in Poisson tails

The uniform bound concerns the symmetric sum. Taking absolute values
before pairing would introduce a divergent harmonic series. The landed
quantitative sawtooth expansion supplies the necessary cancellation.
-/

public section

open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Uniform boundedness of the sawtooth Fourier partial sums, including
integer arguments and the empty zeroth partial sum. -/
theorem norm_sawtoothFourier_le_three (K : ℕ) (x : ℝ) : ‖sawtoothFourier K x‖ ≤ 3 := by
  by_cases hK : K = 0
  · subst K
    norm_num [sawtoothFourier]
  have hmaj : sawtoothMajorant K x ≤ 1 := by
    unfold sawtoothMajorant
    split
    · exact le_rfl
    · exact min_le_right _ _
  have hrem := (norm_sawtoothRem_le (Nat.one_le_iff_ne_zero.mpr hK) x).trans
    (mul_le_mul_of_nonneg_left hmaj (by norm_num : (0 : ℝ) ≤ 5 / 2))
  have hnorm : ‖(sawtooth x : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_sawtooth_le_half x
  have heq : sawtoothFourier K x = (sawtooth x : ℂ) - sawtoothRem K x := by
    unfold sawtoothRem
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith only [hnorm, hrem])

/-- Any block between two symmetric Fourier truncations has a uniform
bound. This is the harmonic cancellation used in the distant Poisson tail. -/
theorem norm_sawtoothFourier_sub_le_six (K L : ℕ) (x : ℝ) :
    ‖sawtoothFourier K x - sawtoothFourier L x‖ ≤ 6 := by
  have hK := norm_sawtoothFourier_le_three K x
  have hL := norm_sawtoothFourier_le_three L x
  exact (norm_sub_le _ _).trans (by linarith only [hK, hL])

end WaveTurbulence.VdCB
