/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.ScalarPowerKernel
public import WaveTurbulence.Foundations.SumintPar.EndpointYoung

/-!
# The two-exit positive-endpoint frequency integral

Asymmetric Young handles the sum of the last two frequencies. A final
Cauchy-Schwarz inequality in the first frequency gives the full L² mass
of the two-variable amplitude. The constants are finite at both required
placements of the order-3/4 denominator.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- Explicit scalar-kernel constant for the two-exit pairing. -/
@[expose] noncomputable def twoExitKernelConstant (a b c : ℝ) : ℝ≥0∞ :=
  (∫⁻ x : ℝ, scalarPowerKernel a x^(2:ℝ))^((1:ℝ)/2) *
    (∫⁻ x : ℝ, scalarPowerKernel b x^((3:ℝ)/2))^((2:ℝ)/3) *
    (∫⁻ x : ℝ, scalarPowerKernel c x^((6:ℝ)/5))^((5:ℝ)/6)

/-- The two-exit constant is finite in the range used by the endpoint split. -/
theorem twoExitKernelConstant_lt_top {a b c : ℝ}
    (ha : 1/2 < a) (hb : 2/3 < b) (hc : 5/6 < c) :
    twoExitKernelConstant a b c < ⊤ := by
  have hm (p q : ℝ) (hq : 0 ≤ q) (hpq : 1 < p*q) :
      (∫⁻ x : ℝ, scalarPowerKernel p x^q) ≠ ⊤ := by
    rw [lintegral_scalarPowerKernel_rpow p hq hpq]
    exact ENNReal.ofReal_ne_top
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hm a 2 (by norm_num) (by linarith)))
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hm b (3/2) (by norm_num) (by linarith))))
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hm c (6/5) (by norm_num) (by linarith)))

/-- The two-exit frequency pairing is bounded by the full two-dimensional L² mass. -/
theorem lintegral_two_exit_kernel_le (a b c : ℝ) (H : ℝ × ℝ → ℝ≥0∞)
    (hH : Measurable H) :
    (∫⁻ x : ℝ, scalarPowerKernel a x * ∫⁻ yz : ℝ × ℝ,
      scalarPowerKernel b yz.1*scalarPowerKernel c yz.2*H (x,yz.1+yz.2)) ≤
      twoExitKernelConstant a b c * (∫⁻ xy : ℝ × ℝ, H xy^(2:ℝ))^((1:ℝ)/2) := by
  let B := (∫⁻ y : ℝ, scalarPowerKernel b y^((3:ℝ)/2))^((2:ℝ)/3) *
    (∫⁻ z : ℝ, scalarPowerKernel c z^((6:ℝ)/5))^((5:ℝ)/6)
  let J := fun x : ℝ => ∫⁻ w : ℝ, H (x,w)^(2:ℝ)
  have hJ : Measurable J := (hH.pow_const (2:ℝ)).lintegral_prod_right'
  have hy (x : ℝ) : (∫⁻ yz : ℝ × ℝ,
      scalarPowerKernel b yz.1*scalarPowerKernel c yz.2*H (x,yz.1+yz.2)) ≤
        B*(J x)^((1:ℝ)/2) :=
    lintegral_triple_add_le_endpoint _ _ (fun w => H (x,w))
      (measurable_scalarPowerKernel _) (measurable_scalarPowerKernel _)
      (hH.comp measurable_prodMk_left)
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℝ)
    (by rw [Real.holderConjugate_iff]; norm_num : (2:ℝ).HolderConjugate 2)
    (measurable_scalarPowerKernel a).aemeasurable (hJ.pow_const ((1:ℝ)/2)).aemeasurable
  change (∫⁻ x : ℝ, scalarPowerKernel a x*(J x)^((1:ℝ)/2)) ≤ _ at hholder
  simp only [← ENNReal.rpow_mul, show ((1:ℝ)/2)*2 = 1 by norm_num,
    ENNReal.rpow_one] at hholder
  have hJI : (∫⁻ x : ℝ, J x) = ∫⁻ xy : ℝ × ℝ, H xy^(2:ℝ) := by
    symm
    change (∫⁻ xy : ℝ × ℝ, H xy^(2:ℝ) ∂((volume : Measure ℝ).prod volume)) = _
    exact lintegral_prod _ (hH.pow_const (2:ℝ)).aemeasurable
  rw [hJI] at hholder
  calc
    _ ≤ ∫⁻ x : ℝ, B*(scalarPowerKernel a x*(J x)^((1:ℝ)/2)) := by
      apply lintegral_mono
      intro x
      exact (mul_le_mul' le_rfl (hy x)).trans_eq (by ac_rfl)
    _ = B*∫⁻ x : ℝ, scalarPowerKernel a x*(J x)^((1:ℝ)/2) :=
      lintegral_const_mul _ ((measurable_scalarPowerKernel a).mul (hJ.pow_const _))
    _ ≤ B*((∫⁻ x : ℝ, scalarPowerKernel a x^(2:ℝ))^((1:ℝ)/2) *
        (∫⁻ xy : ℝ × ℝ, H xy^(2:ℝ))^((1:ℝ)/2)) := mul_le_mul' le_rfl hholder
    _ = _ := by unfold twoExitKernelConstant B; ac_rfl

end WaveTurbulence.SumintPar
