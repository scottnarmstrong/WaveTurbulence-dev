/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.TripleFrequencyCoordinates
public import WaveTurbulence.Foundations.Sumint.EndpointWeightSplit

/-!
# The positive quarter-weight two-exit frequency pairing

The third-frequency weak denominator is exchanged with the second one
before using the asymmetric Young estimate. All constants are absolute
and finite; the full two-dimensional L2 mass remains unchanged.
-/

public section
open MeasureTheory Set ENNReal
namespace WaveTurbulence.Sumint

/-- Exchanging the two summed exit frequencies preserves the native scalar pairing. -/
theorem lintegral_native_two_exit_swap (a b c : ℝ) (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ξ : Fin 3 → ℝ, scalarPowerKernel a (ξ 0)*scalarPowerKernel b (ξ 1)*
      scalarPowerKernel c (ξ 2)*H (ξ 0,ξ 1+ξ 2)) =
    (∫⁻ ξ : Fin 3 → ℝ, scalarPowerKernel a (ξ 0)*scalarPowerKernel c (ξ 1)*
      scalarPowerKernel b (ξ 2)*H (ξ 0,ξ 1+ξ 2)) := by
  rw [lintegral_native_two_exit_eq a b c H hH,lintegral_native_two_exit_eq a c b H hH]
  apply lintegral_congr
  intro x
  congr 1
  let f (yz : ℝ × ℝ) := scalarPowerKernel c yz.1*scalarPowerKernel b yz.2*H (x,yz.1+yz.2)
  calc
    _ = ∫⁻ yz : ℝ × ℝ, f yz.swap := by
      apply lintegral_congr
      intro yz
      dsimp [f]
      rw [add_comm yz.2 yz.1]
      ring
    _ = _ := by
      rw [Measure.volume_eq_prod]
      exact lintegral_prod_swap f

/-- The explicit absolute two-exit quarter-weight constant. -/
@[expose] noncomputable def nativeTwoExitKernelConstant : ℝ≥0∞ :=
  twoExitKernelConstant ((3:ℝ)/4) 1 1 +
    twoExitKernelConstant 1 ((3:ℝ)/4) 1 + twoExitKernelConstant 1 ((3:ℝ)/4) 1

/-- Every term in the native two-exit quarter-weight constant is finite. -/
theorem nativeTwoExitKernelConstant_lt_top : nativeTwoExitKernelConstant < ⊤ := by
  unfold nativeTwoExitKernelConstant
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨twoExitKernelConstant_lt_top (by norm_num) (by norm_num) (by norm_num),
      twoExitKernelConstant_lt_top (by norm_num) (by norm_num) (by norm_num)⟩,
    twoExitKernelConstant_lt_top (by norm_num) (by norm_num) (by norm_num)⟩

/-- Native three-frequency quarter-weight pairing is bounded by the complete two-exit L2 norm. -/
theorem lintegral_native_two_exit_quarter_le (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ξ : Fin 3 → ℝ, Fourier.timeWeight ((1:ℝ)/4) ξ*scalarPowerKernel 1 (ξ 0)*
      scalarPowerKernel 1 (ξ 1)*scalarPowerKernel 1 (ξ 2)*H (ξ 0,ξ 1+ξ 2)) ≤
      nativeTwoExitKernelConstant*(∫⁻ q : ℝ × ℝ, H q^(2:ℝ))^((1:ℝ)/2) := by
  let f (a b c : ℝ) (ξ : Fin 3 → ℝ) := scalarPowerKernel a (ξ 0)*scalarPowerKernel b (ξ 1)*
    scalarPowerKernel c (ξ 2)*H (ξ 0,ξ 1+ξ 2)
  have hcoord : Measurable (fun ξ : Fin 3 → ℝ => (ξ 0,ξ 1+ξ 2)) := by fun_prop
  have hm (a b c : ℝ) : Measurable (f a b c) :=
    ((((measurable_scalarPowerKernel a).comp (measurable_pi_apply 0)).mul
      ((measurable_scalarPowerKernel b).comp (measurable_pi_apply 1))).mul
      ((measurable_scalarPowerKernel c).comp (measurable_pi_apply 2))).mul (hH.comp hcoord)
  have hb (a b c : ℝ) : (∫⁻ ξ, f a b c ξ) ≤
      twoExitKernelConstant a b c*(∫⁻ q : ℝ × ℝ, H q^(2:ℝ))^((1:ℝ)/2) := by
    rw [show (∫⁻ ξ, f a b c ξ) = _ from lintegral_native_two_exit_eq a b c H hH]
    exact lintegral_two_exit_kernel_le a b c H hH
  calc
    _ ≤ ∫⁻ ξ, (f ((3:ℝ)/4) 1 1 ξ+f 1 ((3:ℝ)/4) 1 ξ)+f 1 1 ((3:ℝ)/4) ξ := by
      apply lintegral_mono
      intro ξ
      have he := mul_le_mul' (endpoint_weight_kernel_split ξ) (le_rfl : H (ξ 0,ξ 1+ξ 2) ≤ H (ξ 0,ξ 1+ξ 2))
      simpa only [add_mul,f] using he
    _ = (∫⁻ ξ, f ((3:ℝ)/4) 1 1 ξ)+(∫⁻ ξ, f 1 ((3:ℝ)/4) 1 ξ)+(∫⁻ ξ, f 1 1 ((3:ℝ)/4) ξ) := by
      have hm12 : Measurable (fun ξ => f ((3:ℝ)/4) 1 1 ξ+f 1 ((3:ℝ)/4) 1 ξ) :=
        (hm _ _ _).add (hm _ _ _)
      rw [lintegral_add_left hm12,lintegral_add_left (hm _ _ _)]
    _ ≤ _ := by
      rw [show (∫⁻ ξ, f 1 1 ((3:ℝ)/4) ξ) = ∫⁻ ξ, f 1 ((3:ℝ)/4) 1 ξ from
        lintegral_native_two_exit_swap 1 1 ((3:ℝ)/4) H hH]
      exact (add_le_add (add_le_add (hb _ _ _) (hb _ _ _)) (hb _ _ _)).trans_eq
        (by unfold nativeTwoExitKernelConstant; ring)

end WaveTurbulence.Sumint
