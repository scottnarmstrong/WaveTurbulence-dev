/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Bounded primitives for the sine kernel

Integration by parts gives the Dirichlet bound for `sin(t)/t`. This is the
oscillatory cancellation needed for frequency-uniform principal-value estimates
in DH21 Lemma 6.3, as opposed to absolute bounds using derivatives of the phase.
-/

public section

open MeasureTheory Set
open scoped Topology

namespace WaveTurbulence.Resonant

/-- Dirichlet tail bound away from the singularity. -/
theorem abs_integral_sin_div_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |∫ t in a..b, Real.sin t / t| ≤ 2 * a⁻¹ := by
  have hx : ∀ x ∈ uIcc a b, x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact (ha.trans_le hx.1).ne'
  have hcInv : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc a b) :=
    continuousOn_id.inv₀ hx
  have hcSq : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (uIcc a b) :=
    (continuousOn_id.pow 2).inv₀ (fun x h => pow_ne_zero 2 (hx x h))
  have hiSq : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume a b := hcSq.intervalIntegrable
  have hiSin : IntervalIntegrable (fun t => Real.sin t * t⁻¹) volume a b :=
    (Real.continuous_sin.intervalIntegrable a b).mul_continuousOn hcInv
  have hiCos : IntervalIntegrable (fun t => Real.cos t * (t ^ 2)⁻¹) volume a b :=
    (Real.continuous_cos.intervalIntegrable a b).mul_continuousOn hcSq
  have hip := intervalIntegral.integral_deriv_mul_eq_sub
    (u := -Real.cos) (u' := Real.sin)
    (v := fun x : ℝ => x⁻¹) (v' := fun x : ℝ => -(x ^ 2)⁻¹)
    (fun x _ => by simpa only [neg_neg] using (Real.hasDerivAt_cos x).neg)
    (fun x h => hasDerivAt_inv (hx x h))
    (Real.continuous_sin.intervalIntegrable a b) hiSq.neg
  have hip' : (∫ t in a..b, Real.sin t * t⁻¹) +
      (∫ t in a..b, Real.cos t * (t ^ 2)⁻¹) =
      -Real.cos b * b⁻¹ - -Real.cos a * a⁻¹ := by
    simpa only [Pi.neg_apply, neg_mul_neg, intervalIntegral.integral_add hiSin hiCos] using hip
  have hsq : (∫ t in a..b, (t ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := -(fun x : ℝ => x⁻¹))
      (fun x h => by simpa only [neg_neg] using (hasDerivAt_inv (hx x h)).neg) hiSq
    simp only [Pi.neg_apply] at h
    linarith
  have hcos : |∫ t in a..b, Real.cos t * (t ^ 2)⁻¹| ≤ a⁻¹ - b⁻¹ := by
    rw [← Real.norm_eq_abs, ← hsq]
    apply intervalIntegral.norm_integral_le_of_norm_le hab _ hiSq
    refine Filter.Eventually.of_forall fun t _ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (sq_nonneg t)) (Real.abs_cos_le_one t)
  have hb : 0 < b := ha.trans_le hab
  have hboundary : |-Real.cos b * b⁻¹ - -Real.cos a * a⁻¹| ≤ b⁻¹ + a⁻¹ := by
    refine (abs_sub _ _).trans ?_
    simp only [abs_mul, abs_neg, abs_of_pos (inv_pos.mpr ha), abs_of_pos (inv_pos.mpr hb)]
    exact add_le_add (mul_le_of_le_one_left (inv_nonneg.mpr hb.le) (Real.abs_cos_le_one b))
      (mul_le_of_le_one_left (inv_nonneg.mpr ha.le) (Real.abs_cos_le_one a))
  rw [show (fun t : ℝ => Real.sin t / t) = fun t => Real.sin t * t⁻¹ by
    funext t; rw [div_eq_mul_inv]]
  have he : (∫ t in a..b, Real.sin t * t⁻¹) =
      (-Real.cos b * b⁻¹ - -Real.cos a * a⁻¹) -
        ∫ t in a..b, Real.cos t * (t ^ 2)⁻¹ := by linarith
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hboundary hcos).trans_eq (by ring))

/-- A continuous primitive of the sine kernel, with the removable singularity filled. -/
@[expose] noncomputable def sinePrimitive (x : ℝ) : ℝ :=
  ∫ t in 0..x, Real.sinc t

@[simp] theorem sinePrimitive_zero : sinePrimitive 0 = 0 := by
  simp [sinePrimitive]

/-- Fundamental theorem of calculus for the sine-kernel primitive. -/
theorem hasDerivAt_sinePrimitive (x : ℝ) :
    HasDerivAt sinePrimitive (Real.sinc x) x :=
  intervalIntegral.integral_hasDerivAt_right
    (Real.continuous_sinc.intervalIntegrable 0 x)
    (Real.continuous_sinc.stronglyMeasurableAtFilter _ _)
    Real.continuous_sinc.continuousAt

/-- The primitive is odd because the sine kernel is even. -/
theorem sinePrimitive_neg (x : ℝ) : sinePrimitive (-x) = -sinePrimitive x := by
  unfold sinePrimitive
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := x) Real.sinc
  simp only [Real.sinc_neg, neg_zero] at h
  rw [intervalIntegral.integral_symm (f := Real.sinc) 0 (-x)] at h
  linarith

/-- Dirichlet's uniform primitive bound. -/
theorem abs_sinePrimitive_le (x : ℝ) : |sinePrimitive x| ≤ 3 := by
  suffices hpos : ∀ y : ℝ, 0 ≤ y → |sinePrimitive y| ≤ 3 by
    by_cases hx : 0 ≤ x
    · exact hpos x hx
    · simpa only [sinePrimitive_neg, abs_neg] using hpos (-x) (by linarith)
  intro y hy
  have hsmall : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → |sinePrimitive z| ≤ 1 := by
    intro z hz hz1
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := z) (C := (1 : ℝ)) (f := Real.sinc)
      (fun t _ => by simpa only [Real.norm_eq_abs] using Real.abs_sinc_le_one t)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hz, one_mul] at h
    exact h.trans hz1
  by_cases hy1 : y ≤ 1
  · exact (hsmall y hy hy1).trans (by norm_num)
  · have h1y : 1 ≤ y := (lt_of_not_ge hy1).le
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (Real.continuous_sinc.intervalIntegrable (μ := volume) 0 1)
      (Real.continuous_sinc.intervalIntegrable (μ := volume) 1 y)
    have htail : (∫ t in (1 : ℝ)..y, Real.sinc t) =
        ∫ t in (1 : ℝ)..y, Real.sin t / t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le h1y] at ht
      exact Real.sinc_of_ne_zero (by linarith [ht.1])
    have hbound := abs_integral_sin_div_le (by norm_num : (0 : ℝ) < 1) h1y
    change |∫ t in (0 : ℝ)..y, Real.sinc t| ≤ 3
    rw [← hsplit, htail]
    calc |(∫ t in (0 : ℝ)..1, Real.sinc t) + ∫ t in (1 : ℝ)..y, Real.sin t / t|
        ≤ |sinePrimitive 1| + |∫ t in (1 : ℝ)..y, Real.sin t / t| := abs_add_le _ _
      _ ≤ 1 + 2 * (1 : ℝ)⁻¹ := add_le_add (hsmall 1 (by norm_num) le_rfl) hbound
      _ = 3 := by norm_num

end WaveTurbulence.Resonant
