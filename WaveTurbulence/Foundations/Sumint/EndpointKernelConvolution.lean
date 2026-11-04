/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ConvolutionKernelDecay

/-!
# The ordinary endpoint-kernel convolution

The two inverse-bracket factors have convolution decay 7/8, with explicit
constant `2 * 3^(7/8) * ∫ bracket^(-9/8)`. This decay is sufficient for
the asymmetric Young inequality at the one-exit Fourier endpoint.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- An absolute finite scalar-kernel constant. -/
@[expose] noncomputable def endpointConvolutionConstant : ℝ :=
  2*(3:ℝ)^((7:ℝ)/8) * ∫ x : ℝ, scalarBracket x^(-((9:ℝ)/8))

/-- The displayed absolute constant is nonnegative. -/
theorem endpointConvolutionConstant_nonneg : 0 ≤ endpointConvolutionConstant :=
  mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
    (integral_nonneg (fun _ => Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _))

/-- Real convolution bound for the two ordinary endpoint denominators. -/
theorem integral_endpoint_kernel_convolution_le (t : ℝ) :
    (∫ x : ℝ, scalarBracket x^(-1:ℝ)*scalarBracket (t-x)^(-1:ℝ)) ≤
      endpointConvolutionConstant * scalarBracket t^(-((7:ℝ)/8)) := by
  have hh := integral_scalar_kernel_product_decay (p := 1) (q := 1) (r := (7:ℝ)/8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) t
  simpa only [endpointConvolutionConstant, show (1:ℝ)+1-7/8 = 9/8 by norm_num] using hh

/-- The same convolution bound in the nonnegative form used by Tonelli. -/
theorem lintegral_endpoint_kernel_convolution_le (t : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (scalarBracket x^(-1:ℝ)) *
      ENNReal.ofReal (scalarBracket (t-x)^(-1:ℝ))) ≤
        ENNReal.ofReal endpointConvolutionConstant *
          ENNReal.ofReal (scalarBracket t^(-((7:ℝ)/8))) := by
  have hn (x : ℝ) : 0 ≤ scalarBracket x^(-1:ℝ) :=
    Real.rpow_nonneg (zero_le_one.trans (one_le_scalarBracket _)) _
  have he (x : ℝ) : ENNReal.ofReal (scalarBracket x^(-1:ℝ))*
      ENNReal.ofReal (scalarBracket (t-x)^(-1:ℝ)) =
      ENNReal.ofReal (scalarBracket x^(-1:ℝ)*scalarBracket (t-x)^(-1:ℝ)) :=
    (ENNReal.ofReal_mul (hn x)).symm
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_scalar_kernel_product (a := 1) (b := 1) (by norm_num) (by norm_num) (by norm_num) t)
    (ae_of_all _ (fun x => mul_nonneg (hn x) (hn (t-x)))),
    ← ENNReal.ofReal_mul endpointConvolutionConstant_nonneg]
  exact ENNReal.ofReal_le_ofReal (integral_endpoint_kernel_convolution_le t)

end WaveTurbulence.Sumint
