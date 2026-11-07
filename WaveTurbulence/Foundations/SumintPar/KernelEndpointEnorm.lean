/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.KernelEndpointTransform
public import WaveTurbulence.Foundations.SumintPar.EndpointWeightSplit

/-!
# Nonnegative endpoint representation bound for the actual kernel Fourier transform

This is the exact endpoint norm bound in the extended nonnegative
numbers used by the Fourier norms and scalar kernel integrals.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory ENNReal
namespace WaveTurbulence.SumintPar

/-- The actual kernel Fourier norm is bounded by its two endpoint sums and the native scalar kernels. -/
theorem enorm_timeFourier_kernelExtension_le_exit_transforms {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (c h : ℝ) (F : (D.S.TVar → ℝ) → ℂ)
    (hFm : Measurable F) (hFi : IntegrableOn F (localInputTimeDomain D c h)) (ξ : Fin 3 → ℝ) :
    ‖Fourier.timeFourier (kernelExtension D hI c h F) ξ‖ₑ ≤
      ((∑ v, ‖sourceExitTransform D hI true v F c h (ξ 0) (ξ 1+ξ 2)‖ₑ)+
        (∑ v, ‖sourceExitTransform D hI false v F c h (ξ 0) (ξ 1+ξ 2)‖ₑ))*
        scalarPowerKernel 1 (ξ 0)*scalarPowerKernel 1 (ξ 1)*scalarPowerKernel 1 (ξ 2) := by
  have hden (j : Fin 3) : 0 ≤ 1/scalarBracket (ξ j) := div_nonneg zero_le_one (zero_le_one.trans (one_le_scalarBracket _))
  have hsum (upper : Bool) : 0 ≤ ∑ v, ‖sourceExitTransform D hI upper v F c h (ξ 0) (ξ 1+ξ 2)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have he := ENNReal.ofReal_le_ofReal (norm_timeFourier_kernelExtension_le_exit_transforms D hI c h F hFm hFi ξ)
  rw [ofReal_norm,ENNReal.ofReal_mul (add_nonneg (hsum true) (hsum false)),
    ENNReal.ofReal_add (hsum true) (hsum false)] at he
  simp only [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),ofReal_norm] at he
  rw [Fin.prod_univ_three,ENNReal.ofReal_mul (mul_nonneg (hden 0) (hden 1)),
    ENNReal.ofReal_mul (hden 0)] at he
  simpa only [scalarPowerKernel_one,mul_assoc] using he

end WaveTurbulence.SumintPar
