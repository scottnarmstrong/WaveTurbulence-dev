/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# Integrable scalar kernels for the small bilinear time region

The first moment is integrable in dimension at least three. This is the
quantitative input shared by the case (a), case (c), and incoherence gains.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Sumint

/-- The scalar bracket in the landed stationary-phase estimate. -/
@[expose] noncomputable def scalarBracket (s : ℝ) : ℝ := Real.sqrt (1 + s^2)

/-- The scalar bracket is at least one. -/
theorem one_le_scalarBracket (s : ℝ) : 1 ≤ scalarBracket s := by
  change 1 ≤ Real.sqrt (1 + s^2)
  apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by positivity)).mpr
  nlinarith [sq_nonneg s]

/-- The scalar bracket dominates the absolute value. -/
theorem abs_le_scalarBracket (s : ℝ) : |s| ≤ scalarBracket s := by
  change |s| ≤ Real.sqrt (1 + s^2)
  apply (Real.le_sqrt (abs_nonneg s) (by positivity)).mpr
  rw [sq_abs]
  linarith

/-- Inverse integer powers exceeding one are integrable on the real line. -/
theorem integrable_scalarBracket_inv_pow {p : ℕ} (hp : 1 < p) :
    Integrable (fun s : ℝ => 1 / scalarBracket s^p) := by
  have hi := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
    (r := (p : ℝ)) (by simpa using (show (1 : ℝ) < p by exact_mod_cast hp))
  apply hi.congr
  filter_upwards [] with s
  rw [Real.norm_eq_abs, sq_abs]
  have he : 1 / scalarBracket s^p = (1 + s^2)^(-(p : ℝ)/2) := by
    unfold scalarBracket
    calc
      _ = (Real.sqrt (1 + s^2))^(-(p : ℝ)) := by
        rw [Real.rpow_neg (Real.sqrt_nonneg _), Real.rpow_natCast, one_div]
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1+s^2)]
        congr 1
        ring
  exact he.symm

/-- One power of time is absorbed at the cost of one bracket power. -/
theorem first_moment_kernel_le {d : ℕ} (hd : 1 ≤ d) (s : ℝ) :
    (1 + |s|) / scalarBracket s^d ≤ 2 / scalarBracket s^(d-1) := by
  have hb : 0 < scalarBracket s := lt_of_lt_of_le zero_lt_one (one_le_scalarBracket s)
  have hh : 1 + |s| ≤ 2 * scalarBracket s := by
    linarith [one_le_scalarBracket s, abs_le_scalarBracket s]
  have hp : scalarBracket s^d = scalarBracket s^(d-1) * scalarBracket s := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    _ ≤ (2 * scalarBracket s) / scalarBracket s^d :=
      div_le_div_of_nonneg_right hh (pow_nonneg hb.le _)
    _ = _ := by rw [hp]; field_simp

/-- The stationary-phase kernel with a first time moment is integrable for `d≥3`. -/
theorem integrable_first_moment_kernel {d : ℕ} (hd : 3 ≤ d) :
    Integrable (fun s : ℝ => (1 + |s|) / scalarBracket s^d) := by
  have hi := (integrable_scalarBracket_inv_pow (p := d-1) (by omega)).const_mul 2
  apply hi.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.div
    · fun_prop
    · unfold scalarBracket
      fun_prop
    · intro s
      exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_scalarBracket s)))
  · apply ae_of_all
    intro s
    have hb0 : 0 ≤ scalarBracket s := zero_le_one.trans (one_le_scalarBracket s)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) (pow_nonneg hb0 _))]
    simpa only [mul_one_div] using first_moment_kernel_le (by omega : 1 ≤ d) s

end WaveTurbulence.Sumint
