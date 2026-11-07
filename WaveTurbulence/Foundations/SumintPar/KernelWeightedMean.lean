/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.NegativeEndpointKernel
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic

/-!
# Weighted arithmetic means for scalar bracket kernels

The two factors have the same integrable power after applying the
weighted arithmetic-geometric mean inequality. Translation invariance
then bounds their convolution without invoking a separate Young theorem.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace WaveTurbulence.SumintPar

/-- A product of two scalar kernels is bounded by a weighted sum at the
combined exponent. -/
theorem scalar_kernel_product_le_weighted_sum {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : ℝ) :
    scalarBracket x^(-a)*scalarBracket y^(-b) ≤
      (a/(a+b))*scalarBracket x^(-(a+b)) + (b/(a+b))*scalarBracket y^(-(a+b)) := by
  have hs : 0 < a+b := add_pos ha hb
  have hw : a/(a+b)+b/(a+b) = 1 := by field_simp
  have hh := Real.geom_mean_le_arith_mean2_weighted
    (div_nonneg ha.le hs.le) (div_nonneg hb.le hs.le)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket x)) (-(a+b)))
    (Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket y)) (-(a+b))) hw
  have he (z q : ℝ) : (scalarBracket z^(-(a+b)))^(q/(a+b)) = scalarBracket z^(-q) := by
    rw [← Real.rpow_mul (zero_le_one.trans (one_le_scalarBracket z))]
    congr 1
    field_simp
  simpa only [he] using hh

/-- Kernels whose combined exponent exceeds one have a uniformly bounded
convolution mass. -/
theorem integral_scalar_kernel_product_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 1 < a+b) (t : ℝ) :
    (∫ x : ℝ, scalarBracket x^(-a)*scalarBracket (t-x)^(-b)) ≤
      ∫ x : ℝ, scalarBracket x^(-(a+b)) := by
  have hi := integrable_scalarBracket_rpow hs
  have hi' : Integrable (fun x : ℝ => scalarBracket (t-x)^(-(a+b))) :=
    (integrable_comp_sub_left (μ := (volume : Measure ℝ))
      (fun x : ℝ => scalarBracket x^(-(a+b))) t).mpr hi
  have hsum := (hi.const_mul (a/(a+b))).add (hi'.const_mul (b/(a+b)))
  calc
    _ ≤ ∫ x : ℝ, (a/(a+b))*scalarBracket x^(-(a+b)) +
        (b/(a+b))*scalarBracket (t-x)^(-(a+b)) := by
      apply integral_mono_of_nonneg
        (ae_of_all _ (fun _ => mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _)
          (Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _))) hsum
      exact ae_of_all _ (fun x => scalar_kernel_product_le_weighted_sum ha hb x (t-x))
    _ = _ := by
      rw [integral_add (hi.const_mul _) (hi'.const_mul _), integral_const_mul, integral_const_mul]
      have he := integral_sub_left_eq_self
        (fun x : ℝ => scalarBracket x^(-(a+b))) (volume : Measure ℝ) t
      rw [he]
      have hw : a/(a+b)+b/(a+b) = 1 := by field_simp
      rw [← add_mul, hw, one_mul]

/-- The same weighted-mean majorant proves genuine product integrability. -/
theorem integrable_scalar_kernel_product {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 1 < a+b) (t : ℝ) :
    Integrable (fun x : ℝ => scalarBracket x^(-a)*scalarBracket (t-x)^(-b)) := by
  have hi := integrable_scalarBracket_rpow hs
  have hi' : Integrable (fun x : ℝ => scalarBracket (t-x)^(-(a+b))) :=
    (integrable_comp_sub_left (μ := (volume : Measure ℝ))
      (fun x : ℝ => scalarBracket x^(-(a+b))) t).mpr hi
  have hsum := (hi.const_mul (a/(a+b))).add (hi'.const_mul (b/(a+b)))
  have hk (p : ℝ) : Continuous (fun x : ℝ => scalarBracket x^(-p)) := by
    have hc : Continuous scalarBracket := by unfold scalarBracket; fun_prop
    exact hc.rpow_const (fun x => Or.inl (zero_lt_one.trans_le (one_le_scalarBracket x)).ne')
  apply hsum.mono'
  · exact ((hk a).mul ((hk b).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _)
      (Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _))]
    exact scalar_kernel_product_le_weighted_sum ha hb x (t-x)

end WaveTurbulence.SumintPar
