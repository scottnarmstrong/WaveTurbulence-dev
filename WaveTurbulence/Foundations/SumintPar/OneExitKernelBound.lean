/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.OneExitKernelReduction

/-!
# The one-exit positive-endpoint frequency integral

Convolution decay followed by asymmetric Young bounds the three-frequency
pairing by the L² mass of its single sum-frequency amplitude. All scalar
constants are absolute, explicit and finite.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- The explicit absolute constant in the one-exit frequency estimate. -/
@[expose] noncomputable def oneExitKernelConstant : ℝ≥0∞ :=
  ENNReal.ofReal endpointConvolutionConstant *
    (∫⁻ x : ℝ, scalarPowerKernel ((3:ℝ)/4) x^((3:ℝ)/2))^((2:ℝ)/3) *
    (∫⁻ x : ℝ, scalarPowerKernel ((7:ℝ)/8) x^((6:ℝ)/5))^((5:ℝ)/6)

/-- Every factor in the explicit one-exit constant is finite. -/
theorem oneExitKernelConstant_lt_top : oneExitKernelConstant < ⊤ := by
  have hf : (∫⁻ x : ℝ, scalarPowerKernel ((3:ℝ)/4) x^((3:ℝ)/2)) ≠ ⊤ := by
    rw [lintegral_scalarPowerKernel_rpow _ (by norm_num) (by norm_num)]
    exact ENNReal.ofReal_ne_top
  have hg : (∫⁻ x : ℝ, scalarPowerKernel ((7:ℝ)/8) x^((6:ℝ)/5)) ≠ ⊤ := by
    rw [lintegral_scalarPowerKernel_rpow _ (by norm_num) (by norm_num)]
    exact ENNReal.ofReal_ne_top
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hf))
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hg)

/-- The one-exit frequency pairing has an absolute L² bound. -/
theorem lintegral_one_exit_kernel_le (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x : ℝ, scalarPowerKernel ((3:ℝ)/4) x *
      (∫⁻ y : ℝ, ∫⁻ z : ℝ, scalarPowerKernel 1 y*scalarPowerKernel 1 z*H (x+y+z))) ≤
      oneExitKernelConstant * (∫⁻ s : ℝ, H s^(2:ℝ))^((1:ℝ)/2) := by
  have hy := lintegral_triple_add_le_endpoint (scalarPowerKernel ((3:ℝ)/4))
    (scalarPowerKernel ((7:ℝ)/8)) H (measurable_scalarPowerKernel _)
    (measurable_scalarPowerKernel _) hH
  exact (lintegral_one_exit_reduce_le H hH).trans
    ((mul_le_mul' le_rfl hy).trans_eq (by unfold oneExitKernelConstant; ac_rfl))

end WaveTurbulence.SumintPar
