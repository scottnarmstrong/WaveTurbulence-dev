/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ConvolutionKernelPointwise
public import WaveTurbulence.Foundations.SumintPar.KernelWeightedMean

/-!
# Decay of scalar bracket convolutions

The output weight is distributed pointwise and each remaining product
is controlled by a single integrable power using weighted arithmetic
means. This supplies the non-borderline convolution bound needed for
the one-exit Fourier endpoint.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory

namespace WaveTurbulence.SumintPar

/-- The convolution retains any positive decay below both input exponents
and their sum minus one. The displayed constant is explicit. -/
theorem integral_scalar_kernel_product_decay {p q r : ℝ}
    (hr : 0 ≤ r) (hpr : r < p) (hqr : r < q) (hs : 1 < p+q-r) (t : ℝ) :
    (∫ x : ℝ, scalarBracket x^(-p)*scalarBracket (t-x)^(-q)) ≤
      (2*(3:ℝ)^r * ∫ x : ℝ, scalarBracket x^(-(p+q-r))) * scalarBracket t^(-r) := by
  have hp : 0 < p := hr.trans_lt hpr
  have hq : 0 < q := hr.trans_lt hqr
  have hs1 : 1 < (p-r)+q := by linarith only [hs]
  have hs2 : 1 < p+(q-r) := by linarith only [hs]
  have hi1 := integrable_scalar_kernel_product (sub_pos.mpr hpr) hq hs1 t
  have hi2 := integrable_scalar_kernel_product hp (sub_pos.mpr hqr) hs2 t
  have hb1 := integral_scalar_kernel_product_le (sub_pos.mpr hpr) hq hs1 t
  have hb2 := integral_scalar_kernel_product_le hp (sub_pos.mpr hqr) hs2 t
  have he1 : (p-r)+q = p+q-r := by ring
  have he2 : p+(q-r) = p+q-r := by ring
  rw [he1] at hb1
  rw [he2] at hb2
  have h3 : 0 ≤ (3:ℝ)^r := Real.rpow_nonneg (by norm_num) _
  have hb : scalarBracket t^r *
      (∫ x : ℝ, scalarBracket x^(-p)*scalarBracket (t-x)^(-q)) ≤
        2*(3:ℝ)^r * ∫ x : ℝ, scalarBracket x^(-(p+q-r)) := by
    rw [← integral_const_mul]
    calc
      _ ≤ ∫ x : ℝ, (3:ℝ)^r * (scalarBracket x^(-(p-r))*scalarBracket (t-x)^(-q) +
          scalarBracket x^(-p)*scalarBracket (t-x)^(-(q-r))) := by
        apply integral_mono_of_nonneg
          (ae_of_all _ (fun _ => mul_nonneg
            (Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _)
            (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _)
              (Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _))))
          ((hi1.add hi2).const_mul _)
        apply ae_of_all
        intro x
        have hh := scalar_kernel_weighted_product_le p q r x (t-x) hr
        have ht : x+(t-x) = t := by ring
        rw [ht] at hh
        convert hh using 1; ring
      _ = (3:ℝ)^r * ((∫ x : ℝ, scalarBracket x^(-(p-r))*scalarBracket (t-x)^(-q)) +
          ∫ x : ℝ, scalarBracket x^(-p)*scalarBracket (t-x)^(-(q-r))) := by
        rw [integral_const_mul, integral_add hi1 hi2]
      _ ≤ (3:ℝ)^r * ((∫ x : ℝ, scalarBracket x^(-(p+q-r))) +
          ∫ x : ℝ, scalarBracket x^(-(p+q-r))) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) h3
      _ = _ := by ring
  have ht : 0 < scalarBracket t^r :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le (one_le_scalarBracket _)) _
  rw [Real.rpow_neg (zero_le_one.trans (one_le_scalarBracket t)), ← div_eq_mul_inv]
  apply (le_div_iff₀ ht).mpr
  simpa only [mul_comm] using hb

end WaveTurbulence.SumintPar
