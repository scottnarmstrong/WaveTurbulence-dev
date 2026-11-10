/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.Chi0
public import WaveTurbulence.Foundations.Fourier.GlueGevrey
public import WaveTurbulence.Foundations.Fourier.GevreyInverse
import Mathlib.Tactic

/-!
# Explicit Gevrey constants for the fixed cutoff

TARGET L623, corrected by owner ruling F41. The constants for the scalar
cutoff are `C = exp 4` and `A = 16 + 16 * exp 2`. They are absolute and
uniform in derivative order and position.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

private theorem glue_reflected_bound :
    GevreyTwoBound (fun x => expNegInvGlue (1 - x)) 1 2 := by
  have h := expNegInvGlue_gevreyTwoBound.comp_affine expNegInvGlue.contDiff (-1) 1
  simpa only [abs_neg, abs_one, one_mul, neg_one_mul, neg_add_eq_sub] using h

private theorem transition_denom_lower (x : ℝ) :
    Real.exp (-2) ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  have he : expNegInvGlue (1 / 2) = Real.exp (-2) := by norm_num [expNegInvGlue]
  rcases le_total (1 / 2 : ℝ) x with hx | hx
  · have h := expNegInvGlue.monotone hx
    rw [he] at h
    exact h.trans (le_add_of_nonneg_right (expNegInvGlue.nonneg _))
  · have h := expNegInvGlue.monotone (show (1 / 2 : ℝ) ≤ 1 - x by linarith)
    rw [he] at h
    exact h.trans (le_add_of_nonneg_left (expNegInvGlue.nonneg _))

/-- The standard `exp(-1/x)` transition is Gevrey 2 with explicit constants. -/
theorem smoothTransition_gevreyTwoBound :
    GevreyTwoBound Real.smoothTransition (Real.exp 2) (4 + 4 * Real.exp 2) := by
  have hden : GevreyTwoBound
      (fun x => expNegInvGlue x + expNegInvGlue (1 - x)) 2 2 := by
    simpa only [one_add_one_eq_two] using
      expNegInvGlue_gevreyTwoBound.add glue_reflected_bound
        expNegInvGlue.contDiff (by fun_prop)
  have hinv := hden.inv (by fun_prop) (by norm_num) (by norm_num)
    (Real.exp_pos (-2)) transition_denom_lower
  have hm := expNegInvGlue_gevreyTwoBound.mul hinv
    expNegInvGlue.contDiff
    ((show ContDiff ℝ ∞ (fun x => expNegInvGlue x + expNegInvGlue (1 - x)) by
      fun_prop).inv (fun x => (Real.smoothTransition.pos_denom x).ne'))
    (by norm_num) (by positivity) (by norm_num) (by positivity)
  have he : (Real.exp (-2))⁻¹ = Real.exp 2 := by rw [Real.exp_neg, inv_inv]
  convert hm using 1
  · funext x
    exact div_eq_mul_inv _ _
  · rw [he, one_mul]
  · rw [div_eq_mul_inv, he]
    ring

/-- TARGET L623 with erratum F41: the fixed cutoff has absolute constants
`C = exp 4`, `A = 16 + 16 * exp 2` in the bound
`|χ₀⁽ᵐ⁾(x)| ≤ C * A^m * (2*m)!`. -/
theorem chi0_gevreyTwoBound :
    GevreyTwoBound chi0 (Real.exp 4) (16 + 16 * Real.exp 2) := by
  have hleft := smoothTransition_gevreyTwoBound.comp_affine
    Real.smoothTransition.contDiff (-2) 2
  have hright := smoothTransition_gevreyTwoBound.comp_affine
    Real.smoothTransition.contDiff 2 2
  have hm := hleft.mul hright (by fun_prop) (by fun_prop)
    (by positivity) (by positivity) (by positivity) (by positivity)
  convert hm using 1
  · funext x
    simp only [chi0]
    congr 1 <;> congr 1 <;> ring
  · rw [← Real.exp_add]
    norm_num
  · norm_num
    ring

/-- The complementary cutoff is Gevrey 2 with the same exponential constant. -/
theorem chiInfinity_gevreyTwoBound :
    GevreyTwoBound chiInfinity (1 + Real.exp 4) (16 + 16 * Real.exp 2) := by
  have hc := (gevreyTwoBound_const 1).mono (by norm_num) (by norm_num)
    (show |(1 : ℝ)| ≤ 1 by norm_num) (show 0 ≤ 16 + 16 * Real.exp 2 by positivity)
  exact hc.add chi0_gevreyTwoBound.neg contDiff_const chi0_contDiff.neg

end WaveTurbulence.Fourier
