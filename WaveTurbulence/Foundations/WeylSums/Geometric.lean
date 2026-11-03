/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.Basic
public import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Linear sums and distance to the integers

The geometric-series ingredient in the Weyl differencing route to DH23's
Gauss lemma. The norm on `AddCircle 1` is distance to the nearest integer.
At integral frequencies the trivial bound must be used instead of an inverse
distance (Lean's inverse of zero is zero).
-/

public section

namespace WaveTurbulence.WeylSums

@[simp] theorem e_int (m : ℤ) : e m = 1 := by
  unfold e
  rw [show ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I =
      (m : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

theorem e_sub_int (t : ℝ) (m : ℤ) : e (t - m) = e t := by
  rw [e_sub, e_int, div_one]

/-- Quantitative separation of the additive exponential from `1`. -/
theorem four_mul_norm_addCircle_le (t : ℝ) :
    4 * ‖(t : AddCircle (1 : ℝ))‖ ≤ ‖e t - 1‖ := by
  have hdist : ‖(t : AddCircle (1 : ℝ))‖ = |t - round t| := by
    simpa only [inv_one, one_mul, mul_one] using (AddCircle.norm_eq (p := (1 : ℝ)) (x := t))
  have hs : 2 / Real.pi * |Real.pi * (t - round t)| ≤
      |Real.sin (Real.pi * (t - round t))| := by
    apply Real.mul_abs_le_abs_sin
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left (abs_sub_round t) Real.pi_pos.le).trans_eq (by ring)
  have hs' : 2 * |t - round t| ≤ |Real.sin (Real.pi * (t - round t))| := by
    convert hs using 1
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [hdist, ← e_sub_int t (round t)]
  have hexp : e (t - round t) =
      Complex.exp (Complex.I * (2 * Real.pi * (t - round t) : ℝ)) := by
    unfold e
    rw [mul_comm]
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have harg : 2 * Real.pi * (t - round t) / 2 = Real.pi * (t - round t) := by ring
  rw [harg]
  linarith only [hs']

/-- The usual inverse-distance estimate for a nonintegral frequency. -/
theorem norm_linearSum_le_inv_distance (t : ℝ) (N : ℕ)
    (ht : (t : AddCircle (1 : ℝ)) ≠ 0) :
    ‖linearSum t N‖ ≤ 1 / (2 * ‖(t : AddCircle (1 : ℝ))‖) := by
  have hd : 0 < ‖(t : AddCircle (1 : ℝ))‖ := norm_pos_iff.mpr ht
  have hsep := four_mul_norm_addCircle_le t
  have he : e t ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hsep
    linarith only [hsep, hd]
  refine (norm_linearSum_le_geometric t N he).trans ?_
  apply (div_le_div_iff₀ (lt_of_lt_of_le (by positivity : 0 < 4 * ‖(t : AddCircle (1 : ℝ))‖) hsep)
    (by positivity : 0 < 2 * ‖(t : AddCircle (1 : ℝ))‖)).mpr
  linarith only [hsep]

/-- Combined trivial and geometric bounds, away from the resonant frequency. -/
theorem norm_linearSum_le_min (t : ℝ) (N : ℕ)
    (ht : (t : AddCircle (1 : ℝ)) ≠ 0) :
    ‖linearSum t N‖ ≤ min (N : ℝ) (1 / (2 * ‖(t : AddCircle (1 : ℝ))‖)) :=
  le_min (norm_linearSum_le t N) (norm_linearSum_le_inv_distance t N ht)

end WaveTurbulence.WeylSums
