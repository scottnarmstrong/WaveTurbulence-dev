/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.PoissonMarginNegative
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Width-dependent constants in the Poisson truncation error

The normalized frequency count is at most the derivative-range width plus
two. The explicit error therefore has the standard `η⁻¹+log(width+2)` form.
-/

public section

namespace WaveTurbulence.VdCB

/-- A uniform absolute constant for the explicit normalized Poisson error. -/
theorem poisson_error_le_ten {W η : ℝ} (hW : 0 ≤ W) (hη : 0 < η) (hη1 : η ≤ 1)
    (N : ℕ) (hN : (N : ℝ) ≤ W + 2) :
    ((2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) + 1) +
        2 / (Real.pi * η) ≤ 10 * (η⁻¹ + Real.log (W + 2)) := by
  have hbase : 0 < W + 2 := by linarith
  have hlog : 0 ≤ Real.log (W + 2) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num only at hh
    exact hh
  have hlogNp : Real.log ((N : ℝ) + 1) ≤ 1 + Real.log (W + 2) := by
    have hh := Real.log_le_log (by positivity : 0 < (N : ℝ) + 1)
      (show (N : ℝ) + 1 ≤ 2 * (W + 2) by linarith only [hN, hW])
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hbase.ne'] at hh
    linarith only [hh, hlog2]
  have hlogN : Real.log N ≤ 1 + Real.log (W + 2) := by
    by_cases hn : N = 0
    · subst N
      simp only [Nat.cast_zero, Real.log_zero]
      linarith only [hlog]
    · exact (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn)
        (by linarith : (N : ℝ) ≤ (N : ℝ) + 1)).trans hlogNp
  have hlogN0 := Real.log_natCast_nonneg N
  have hlogNp0 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hnum0 : 0 ≤ 2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1) := by linarith only [hlogN0, hlogNp0]
  have hpi : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  have hden : (2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / (2 * Real.pi) ≤
      4 + 3 * Real.log (W + 2) := by
    calc
      _ ≤ (2 * (1 + Real.log N) + 4 * Real.log ((N : ℝ) + 1)) / 2 :=
        div_le_div_of_nonneg_left hnum0 (by norm_num) (by linarith only [hpi])
      _ ≤ _ := by linarith only [hlogN, hlogNp]
  have hηterm : 2 / (Real.pi * η) ≤ 2 / η :=
    div_le_div_of_nonneg_left (by norm_num) hη (by nlinarith only [hpi, hη])
  have hηinv : 1 ≤ η⁻¹ := by
    simpa only [one_div, div_one] using (one_div_le_one_div_of_le hη hη1)
  rw [show (2 : ℝ) / η = 2 * η⁻¹ by ring] at hηterm
  nlinarith only [hden, hηterm, hηinv, hlog]

end WaveTurbulence.VdCB
