/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.NativeOneExitSymmetries
public import WaveTurbulence.Foundations.Sumint.OneExitKernelBound
public import WaveTurbulence.Foundations.Sumint.EndpointWeightSplit

/-!
# The positive quarter-weight one-exit source pairing

Reflection removes the source's first-frequency minus sign. Exchanges
put each weak denominator in the first coordinate before the established
one-exit scalar estimate is applied. The constant is absolute and finite.
-/

public section
open MeasureTheory ENNReal
namespace WaveTurbulence.Sumint

/-- The native sum-frequency pairing with its first weak denominator has the established scalar L2 bound. -/
theorem lintegral_native_one_exit_base_le (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ξ : Fin 3 → ℝ, scalarPowerKernel ((3:ℝ)/4) (ξ 0)*scalarPowerKernel 1 (ξ 1)*
      scalarPowerKernel 1 (ξ 2)*H (ξ 0+ξ 1+ξ 2)) ≤
      oneExitKernelConstant*(∫⁻ s : ℝ, H s^(2:ℝ))^((1:ℝ)/2) := by
  have hsum : Measurable (fun q : ℝ × ℝ => H (q.1+q.2)) := hH.comp (measurable_fst.add measurable_snd)
  calc
    _ = ∫⁻ x : ℝ, scalarPowerKernel ((3:ℝ)/4) x * ∫⁻ y : ℝ, ∫⁻ z : ℝ,
        scalarPowerKernel 1 y*scalarPowerKernel 1 z*H (x+y+z) := by
      have he := lintegral_native_two_exit_eq ((3:ℝ)/4) 1 1 (fun q => H (q.1+q.2)) hsum
      simp only [← add_assoc] at he
      rw [he]
      apply lintegral_congr
      intro x
      congr 1
      rw [Measure.volume_eq_prod]
      have hm : Measurable (fun yz : ℝ × ℝ => scalarPowerKernel 1 yz.1*scalarPowerKernel 1 yz.2*H (x+yz.1+yz.2)) :=
        (((measurable_scalarPowerKernel 1).comp measurable_fst).mul
          ((measurable_scalarPowerKernel 1).comp measurable_snd)).mul
          (hH.comp ((measurable_const.add measurable_fst).add measurable_snd))
      exact lintegral_prod _ hm.aemeasurable
    _ ≤ _ := lintegral_one_exit_kernel_le H hH

/-- The explicit absolute quarter-weight one-exit kernel constant. -/
@[expose] noncomputable def nativeOneExitKernelConstant : ℝ≥0∞ :=
  oneExitKernelConstant+oneExitKernelConstant+oneExitKernelConstant

/-- The native quarter-weight one-exit constant is finite. -/
theorem nativeOneExitKernelConstant_lt_top : nativeOneExitKernelConstant < ⊤ :=
  ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨oneExitKernelConstant_lt_top,oneExitKernelConstant_lt_top⟩,oneExitKernelConstant_lt_top⟩

/-- The native signed source one-exit quarter-weight pairing has an absolute L2 bound. -/
theorem lintegral_native_one_exit_quarter_le (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ξ : Fin 3 → ℝ, Fourier.timeWeight ((1:ℝ)/4) ξ*scalarPowerKernel 1 (ξ 0)*
      scalarPowerKernel 1 (ξ 1)*scalarPowerKernel 1 (ξ 2)*H (ξ 1+ξ 2-ξ 0)) ≤
      nativeOneExitKernelConstant*(∫⁻ s : ℝ, H s^(2:ℝ))^((1:ℝ)/2) := by
  let f (a b c : ℝ) (ξ : Fin 3 → ℝ) := scalarPowerKernel a (ξ 0)*scalarPowerKernel b (ξ 1)*
    scalarPowerKernel c (ξ 2)*H (ξ 1+ξ 2-ξ 0)
  have hcoord : Measurable (fun ξ : Fin 3 → ℝ => ξ 1+ξ 2-ξ 0) := by fun_prop
  have hm (a b c : ℝ) : Measurable (f a b c) :=
    ((((measurable_scalarPowerKernel a).comp (measurable_pi_apply 0)).mul
      ((measurable_scalarPowerKernel b).comp (measurable_pi_apply 1))).mul
      ((measurable_scalarPowerKernel c).comp (measurable_pi_apply 2))).mul (hH.comp hcoord)
  have h0 : (∫⁻ ξ, f ((3:ℝ)/4) 1 1 ξ) ≤ oneExitKernelConstant*(∫⁻ s : ℝ, H s^(2:ℝ))^((1:ℝ)/2) := by
    rw [show (∫⁻ ξ, f ((3:ℝ)/4) 1 1 ξ) = _ from lintegral_native_one_exit_reflect ((3:ℝ)/4) 1 1 H]
    exact lintegral_native_one_exit_base_le H hH
  have h1 : (∫⁻ ξ, f 1 ((3:ℝ)/4) 1 ξ) ≤ oneExitKernelConstant*(∫⁻ s : ℝ, H s^(2:ℝ))^((1:ℝ)/2) := by
    rw [show (∫⁻ ξ, f 1 ((3:ℝ)/4) 1 ξ) = _ from lintegral_native_one_exit_reflect 1 ((3:ℝ)/4) 1 H,
      lintegral_native_one_exit_swap_one 1 ((3:ℝ)/4) 1 H]
    exact lintegral_native_one_exit_base_le H hH
  have h2 : (∫⁻ ξ, f 1 1 ((3:ℝ)/4) ξ) ≤ oneExitKernelConstant*(∫⁻ s : ℝ, H s^(2:ℝ))^((1:ℝ)/2) := by
    rw [show (∫⁻ ξ, f 1 1 ((3:ℝ)/4) ξ) = _ from lintegral_native_one_exit_reflect 1 1 ((3:ℝ)/4) H,
      lintegral_native_one_exit_swap_two 1 1 ((3:ℝ)/4) H]
    exact lintegral_native_one_exit_base_le H hH
  calc
    _ ≤ ∫⁻ ξ, (f ((3:ℝ)/4) 1 1 ξ+f 1 ((3:ℝ)/4) 1 ξ)+f 1 1 ((3:ℝ)/4) ξ := by
      apply lintegral_mono
      intro ξ
      have he := mul_le_mul' (endpoint_weight_kernel_split ξ) (le_rfl : H (ξ 1+ξ 2-ξ 0) ≤ H (ξ 1+ξ 2-ξ 0))
      simpa only [add_mul,f] using he
    _ = (∫⁻ ξ, f ((3:ℝ)/4) 1 1 ξ)+(∫⁻ ξ, f 1 ((3:ℝ)/4) 1 ξ)+(∫⁻ ξ, f 1 1 ((3:ℝ)/4) ξ) := by
      have hm12 : Measurable (fun ξ => f ((3:ℝ)/4) 1 1 ξ+f 1 ((3:ℝ)/4) 1 ξ) := (hm _ _ _).add (hm _ _ _)
      rw [lintegral_add_left hm12,lintegral_add_left (hm _ _ _)]
    _ ≤ _ := (add_le_add (add_le_add h0 h1) h2).trans_eq (by unfold nativeOneExitKernelConstant; ring)

end WaveTurbulence.Sumint
