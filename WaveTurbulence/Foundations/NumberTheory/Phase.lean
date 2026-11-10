/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license; see SALT-LICENSE in this directory.
Authors: Jason Hickey, Claude
Adapted for WaveTurbulence by Scott Armstrong.
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Normalized exponential phases and reciprocal weights

NT-CIRCLE-v2 goal 1: increasing consecutive phase differences in a single
integer strip `[m+δ,m+1-δ]` give a sum bounded by `1/δ`.
The proof uses Abel summation and the monotone imaginary part of
`(1-exp(2πix))⁻¹`. Bounds on fractional parts alone do not suffice.

Adapted from `Salt/ExpSum/Kusmin.lean`, commit
`3d7274047aabeea823abf1c0bdf675ce165dbca2`, https://github.com/jyh/salt.
Only the proved discrete theorem and its lemmas are carried over; the upstream
file's obsolete discussion of a second-derivative constant is omitted.
-/

public section

namespace WaveTurbulence.NumberTheory

open Real Finset

/-- The normalized additive character `exp(2πix)`. -/
@[expose] noncomputable def expPhase (x : ℝ) : ℂ := Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I)

/-- `‖expPhase x‖ = 1`. -/
@[simp] lemma norm_expPhase (x : ℝ) : ‖expPhase x‖ = 1 := by
  simp only [expPhase]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `expPhase (x + y) = expPhase x * expPhase y`. -/
lemma expPhase_add (x y : ℝ) : expPhase (x + y) = expPhase x * expPhase y := by
  simp only [expPhase, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- Periodicity: `expPhase` is unchanged by adding an integer. -/
lemma expPhase_add_intCast (x : ℝ) (k : ℤ) : expPhase (x + (k : ℝ)) = expPhase x := by
  have h : (((2 * π * (x + (k : ℝ))) : ℝ) : ℂ) * Complex.I
      = (((2 * π * x : ℝ)) : ℂ) * Complex.I + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast; ring
  simp only [expPhase, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem expPhase_neg (x : ℝ) : expPhase (-x) = (expPhase x)⁻¹ := by
  simp only [expPhase, Complex.ofReal_neg, mul_neg, neg_mul, Complex.exp_neg]

theorem conj_expPhase (x : ℝ) : (starRingEnd ℂ) (expPhase x) = expPhase (-x) := by
  rw [expPhase_neg]
  exact (Complex.inv_eq_conj (norm_expPhase x)).symm

/-- `expPhase` in real cos/sin form. -/
lemma expPhase_eq_cos_add_sin (s : ℝ) :
    expPhase s = (Real.cos (2 * π * s) : ℂ) + (Real.sin (2 * π * s) : ℂ) * Complex.I := by
  simp only [expPhase, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- `(expPhase s).re = cos (2πs)`. -/
lemma expPhase_re (s : ℝ) : (expPhase s).re = Real.cos (2 * π * s) := by
  rw [expPhase_eq_cos_add_sin]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- `(expPhase s).im = sin (2πs)`. -/
lemma expPhase_im (s : ℝ) : (expPhase s).im = Real.sin (2 * π * s) := by
  rw [expPhase_eq_cos_add_sin]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]

/-- `(1 - expPhase s).re = 2 sin²(πs)`. -/
lemma one_sub_expPhase_re (s : ℝ) : (1 - expPhase s).re = 2 * Real.sin (π * s) ^ 2 := by
  have h1 : (1 - expPhase s).re = 1 - Real.cos (2 * π * s) := by simp [expPhase_re]
  rw [h1, show (2 : ℝ) * π * s = 2 * (π * s) by ring, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (π * s)]

/-- `(1 - expPhase s).im = -2 sin(πs) cos(πs)`. -/
lemma one_sub_expPhase_im (s : ℝ) : (1 - expPhase s).im = -(2 * Real.sin (π * s) * Real.cos (π * s)) := by
  have h1 : (1 - expPhase s).im = -Real.sin (2 * π * s) := by simp [expPhase_im]
  rw [h1, show (2 : ℝ) * π * s = 2 * (π * s) by ring, Real.sin_two_mul]

/-- `normSq (1 - expPhase s) = 4 sin²(πs)`. -/
lemma normSq_one_sub_expPhase (s : ℝ) : Complex.normSq (1 - expPhase s) = 4 * Real.sin (π * s) ^ 2 := by
  rw [Complex.normSq_apply, one_sub_expPhase_re, one_sub_expPhase_im]
  nlinarith [Real.sin_sq_add_cos_sq (π * s)]

/-- Norm of `1 - expPhase s` as `2|sin(πs)|`. -/
lemma norm_one_sub_expPhase (s : ℝ) : ‖1 - expPhase s‖ = 2 * |Real.sin (π * s)| := by
  rw [Complex.norm_def, normSq_one_sub_expPhase]
  rw [show (4 : ℝ) * Real.sin (π * s) ^ 2 = (2 * |Real.sin (π * s)|) ^ 2 by
        rw [mul_pow]; rw [sq_abs]; ring]
  exact Real.sqrt_sq (by positivity)

/-- The telescoping weight. -/
@[expose] noncomputable def reciprocalPhaseWeight (s : ℝ) : ℂ := (1 - expPhase s)⁻¹

/-- `Re (reciprocalPhaseWeight s) = 1/2` (constant!) whenever `sin(πs) ≠ 0`. -/
lemma reciprocalPhaseWeight_re (s : ℝ) (hs : Real.sin (π * s) ≠ 0) : (reciprocalPhaseWeight s).re = 1 / 2 := by
  rw [reciprocalPhaseWeight, Complex.inv_re, normSq_one_sub_expPhase, one_sub_expPhase_re]
  have : Real.sin (π * s) ^ 2 ≠ 0 := pow_ne_zero 2 hs
  field_simp
  ring

/-- `Im (reciprocalPhaseWeight s) = cos(πs)/(2 sin(πs)) = cot(πs)/2`. -/
lemma reciprocalPhaseWeight_im (s : ℝ) (hs : Real.sin (π * s) ≠ 0) :
    (reciprocalPhaseWeight s).im = Real.cos (π * s) / (2 * Real.sin (π * s)) := by
  rw [reciprocalPhaseWeight, Complex.inv_im, normSq_one_sub_expPhase, one_sub_expPhase_im]
  field_simp
  ring

/-- `‖reciprocalPhaseWeight s‖ = 1 / (2|sin(πs)|)`. -/
lemma norm_reciprocalPhaseWeight (s : ℝ) : ‖reciprocalPhaseWeight s‖ = 1 / (2 * |Real.sin (π * s)|) := by
  rw [reciprocalPhaseWeight, norm_inv, norm_one_sub_expPhase, inv_eq_one_div]

/-- `sin(πs) > 0` for `s ∈ (0,1)`. -/
lemma sin_pi_mul_pos {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 0 < Real.sin (π * s) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith only [h1, Real.pi_pos]

/-- Jordan's inequality, symmetrised: `sin(πs) ≥ 2δ` for `s ∈ [δ, 1-δ]`, `δ ≤ 1/2`. -/
lemma sin_pi_mul_ge {δ s : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hs1 : δ ≤ s)
    (hs2 : s ≤ 1 - δ) : 2 * δ ≤ Real.sin (π * s) := by
  have hkey : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → 2 * t ≤ Real.sin (π * t) := by
    intro t ht0 ht1
    have hj := Real.mul_le_sin (x := π * t) (by positivity) (by nlinarith [Real.pi_pos])
    have hid : 2 / π * (π * t) = 2 * t := by field_simp
    linarith [hid ▸ hj]
  by_cases h : s ≤ 1 / 2
  · exact le_trans (by linarith) (hkey s (by linarith) h)
  · replace h := not_le.mp h
    have hsym : Real.sin (π * s) = Real.sin (π * (1 - s)) := by
      rw [show π * (1 - s) = π - π * s by ring, Real.sin_pi_sub]
    rw [hsym]
    exact le_trans (by linarith) (hkey (1 - s) (by linarith) (by linarith))

/-- Monotonicity of `Im (reciprocalPhaseWeight ·) = cot(π ·)/2`: antitone on `(0,1)`. -/
lemma reciprocalPhaseWeight_im_antitone {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h12 : s₁ ≤ s₂) (h2 : s₂ < 1) :
    Real.cos (π * s₂) / (2 * Real.sin (π * s₂))
      ≤ Real.cos (π * s₁) / (2 * Real.sin (π * s₁)) := by
  have hs1 : 0 < Real.sin (π * s₁) := sin_pi_mul_pos h1 (lt_of_le_of_lt h12 h2)
  have hs2 : 0 < Real.sin (π * s₂) := sin_pi_mul_pos (lt_of_lt_of_le h1 h12) h2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsin : 0 ≤ Real.sin (π * s₂ - π * s₁) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith only [h12, Real.pi_pos]
    · nlinarith only [h2, h12, h1, Real.pi_pos, mul_pos Real.pi_pos h1]
  rw [Real.sin_sub] at hsin
  linarith only [hsin]

/-- A purely imaginary complex number has norm equal to `|Im|`. -/
lemma norm_eq_abs_im_of_re_eq_zero {z : ℂ} (h : z.re = 0) : ‖z‖ = |z.im| := by
  rw [Complex.norm_def, Complex.normSq_apply, h, zero_mul, zero_add, ← sq,
    Real.sqrt_sq_eq_abs]

end WaveTurbulence.NumberTheory
