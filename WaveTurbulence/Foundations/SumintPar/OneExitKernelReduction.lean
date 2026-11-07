/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ScalarPowerKernel
public import WaveTurbulence.Foundations.SumintPar.ConvolutionPairingIdentity

/-!
# Collapsing the two ordinary kernels at the one-exit endpoint

The sum-frequency amplitude remains unchanged. Only the two scalar
endpoint denominators are convolved, and their explicit 7/8 decay is
then inserted as a pointwise majorant.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- Two ordinary endpoint denominators reduce to a single kernel of order 7/8. -/
theorem lintegral_one_exit_pair_le (H : ℝ → ℝ≥0∞) (hH : Measurable H) (x : ℝ) :
    (∫⁻ y : ℝ, ∫⁻ z : ℝ, scalarPowerKernel 1 y*scalarPowerKernel 1 z*H (x+y+z)) ≤
      ENNReal.ofReal endpointConvolutionConstant *
        ∫⁻ w : ℝ, scalarPowerKernel ((7:ℝ)/8) w*H (x+w) := by
  rw [lintegral_add_pairing_eq_convolution _ _ H (measurable_scalarPowerKernel 1)
    (measurable_scalarPowerKernel 1) hH x]
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal endpointConvolutionConstant *
        (scalarPowerKernel ((7:ℝ)/8) w*H (x+w)) := by
      apply lintegral_mono
      intro w
      have hb := lintegral_endpoint_kernel_convolution_le w
      change (∫⁻ y : ℝ, scalarPowerKernel 1 y*scalarPowerKernel 1 (w-y)) ≤
        ENNReal.ofReal endpointConvolutionConstant * scalarPowerKernel ((7:ℝ)/8) w at hb
      exact (mul_le_mul' hb le_rfl).trans_eq (by ac_rfl)
    _ = _ := lintegral_const_mul _ ((measurable_scalarPowerKernel _).mul
      (hH.comp (measurable_const.add measurable_id)))

/-- After the two-kernel reduction, the three-frequency pairing is exactly
in the form of the asymmetric two-variable Young inequality. -/
theorem lintegral_one_exit_reduce_le (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x : ℝ, scalarPowerKernel ((3:ℝ)/4) x *
      (∫⁻ y : ℝ, ∫⁻ z : ℝ, scalarPowerKernel 1 y*scalarPowerKernel 1 z*H (x+y+z))) ≤
      ENNReal.ofReal endpointConvolutionConstant *
        ∫⁻ xy : ℝ × ℝ, scalarPowerKernel ((3:ℝ)/4) xy.1 *
          scalarPowerKernel ((7:ℝ)/8) xy.2 * H (xy.1+xy.2) := by
  have hm : Measurable (fun xy : ℝ × ℝ => scalarPowerKernel ((3:ℝ)/4) xy.1 *
      scalarPowerKernel ((7:ℝ)/8) xy.2 * H (xy.1+xy.2)) :=
    (((measurable_scalarPowerKernel _).comp measurable_fst).mul
      ((measurable_scalarPowerKernel _).comp measurable_snd)).mul
        (hH.comp (measurable_fst.add measurable_snd))
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal endpointConvolutionConstant *
        (scalarPowerKernel ((3:ℝ)/4) x * ∫⁻ w : ℝ, scalarPowerKernel ((7:ℝ)/8) w*H (x+w)) := by
      apply lintegral_mono
      intro x
      exact (mul_le_mul' le_rfl (lintegral_one_exit_pair_le H hH x)).trans_eq (by ac_rfl)
    _ = ENNReal.ofReal endpointConvolutionConstant *
        ∫⁻ x : ℝ, scalarPowerKernel ((3:ℝ)/4) x *
          ∫⁻ w : ℝ, scalarPowerKernel ((7:ℝ)/8) w*H (x+w) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      congr 1
      change (∫⁻ x : ℝ, scalarPowerKernel ((3:ℝ)/4) x *
        ∫⁻ w : ℝ, scalarPowerKernel ((7:ℝ)/8) w*H (x+w)) =
          ∫⁻ xy : ℝ × ℝ, scalarPowerKernel ((3:ℝ)/4) xy.1 *
            scalarPowerKernel ((7:ℝ)/8) xy.2 * H (xy.1+xy.2) ∂((volume : Measure ℝ).prod volume)
      rw [lintegral_prod _ hm.aemeasurable]
      apply lintegral_congr
      intro x
      have hmw : AEMeasurable (fun w : ℝ => scalarPowerKernel ((7:ℝ)/8) w*H (x+w)) volume :=
        ((measurable_scalarPowerKernel _).mul
          (hH.comp (measurable_const.add measurable_id))).aemeasurable
      symm
      convert lintegral_const_mul'' (scalarPowerKernel ((3:ℝ)/4) x) hmw using 1
      apply lintegral_congr
      intro w
      ac_rfl

end WaveTurbulence.SumintPar
