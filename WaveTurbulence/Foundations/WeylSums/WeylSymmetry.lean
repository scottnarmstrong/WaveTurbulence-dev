/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.WeylSupremum
public import WaveTurbulence.Foundations.WeylSums.HuaOrthogonality

/-! # Sign symmetry and integer periodicity of the supremum Weyl sum -/

public section
open Finset
namespace WaveTurbulence.WeylSums

/-- A real cutoff makes conjugation reverse both phase frequencies. -/
theorem conj_weyl_sum {L : ℝ} (hL : 0 < L) (t r : ℝ) :
    star (smoothGaussSum weylCutoff L t r 0) = smoothGaussSum weylCutoff L (-t) (-r) 0 := by
  rw [weyl_sum_eq_finite hL, weyl_sum_eq_finite hL]
  simp only [star_sum, star_mul, weylCutoff, Complex.star_def, Complex.conj_ofReal, conj_e]
  apply sum_congr rfl
  intro n hn
  rw [show -(t * (n : ℝ)^2+r*n) = (-t)*(n : ℝ)^2+(-r)*n by ring, mul_comm]

/-- The negative frequencies from diagonalization have the same supremum. -/
theorem weylSupremum_neg {L : ℝ} (hL : 0 < L) (t : ℝ) :
    weylSupremum L (-t) = weylSupremum L t := by
  have hh (u : ℝ) : weylSupremum L (-u) ≤ weylSupremum L u := by
    apply ciSup_le
    intro r
    have heq := congrArg norm (conj_weyl_sum hL u (-r))
    simp only [norm_star, neg_neg] at heq
    rw [← heq]
    exact norm_smoothGaussSum_le_weylSupremum hL u (-r) 0
  exact le_antisymm (hh t) (by simpa only [neg_neg] using hh (-t))

/-- Integer shifts of the quadratic frequency leave every lattice sum fixed. -/
theorem smoothGaussSum_add_int (χ : ℝ → ℂ) (L t r : ℝ) (h k : ℤ) :
    smoothGaussSum χ L (t+k) r h = smoothGaussSum χ L t r h := by
  apply tsum_congr
  intro n
  have heq : (t+(k : ℝ)) * (n : ℝ)^2 + r*n =
      (t * (n : ℝ)^2+r*n) + ((k*n^2 : ℤ) : ℝ) := by push_cast; ring
  rw [heq, e_add, e_int, mul_one]

/-- The supremum is one-periodic in the quadratic frequency. -/
theorem weylSupremum_add_int (L t : ℝ) (k : ℤ) :
    weylSupremum L (t+k) = weylSupremum L t := by
  unfold weylSupremum
  congr 1
  funext r
  rw [smoothGaussSum_add_int]

end WaveTurbulence.WeylSums
