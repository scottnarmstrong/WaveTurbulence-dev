/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.KernelLinearity

/-!
# Absolute time mass of the actual rectangular kernel

The rectangle has absolute output-time mass at most two on the actual
local domain. This is used only for countable recombination, without
changing the oscillatory norm estimates.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
namespace WaveTurbulence.SumintPar

/-- The actual rectangular extension has at most twice the absolute input coefficient mass. -/
theorem integral_norm_kernelExtension_le {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (c h : ℝ) (F : (D.S.TVar → ℝ) → ℂ) (hFm : Measurable F)
    (hFi : IntegrableOn F (localInputTimeDomain D c h)) :
    (∫ z, ‖kernelExtension D hI c h F z‖) ≤
      2*(∫ u in localInputTimeDomain D c h, ‖F u‖) := by
  let μ := volume.restrict (localInputTimeDomain D c h)
  let K := fun u z => F u*exponentialBox (lowerTimeExit D hI u)
    (upperTimeExit D hI u) (u (firstTime D hI)) z
  have hi : Integrable (Function.uncurry K) (μ.prod volume) :=
    integrable_kernelExtension_integrand D hI c h F hFm hFi
  calc
    _ ≤ ∫ z, ∫ u, ‖K u z‖ ∂μ := by
      apply integral_mono (integrable_kernelExtension D hI c h F hFm hFi).norm
        hi.norm.integral_prod_right
      intro z
      exact norm_integral_le_integral_norm _
    _ = ∫ u, (∫ z, ‖K u z‖) ∂μ := integral_integral_swap hi.norm.swap
    _ ≤ ∫ u, ‖F u‖*2 ∂μ := by
      apply integral_mono_ae hi.norm.integral_prod_left (hFi.norm.mul_const 2)
      filter_upwards [ae_restrict_mem (measurableSet_localInputTimeDomain D c h)] with u hu
      change (∫ z, ‖F u*exponentialBox (lowerTimeExit D hI u) (upperTimeExit D hI u)
        (u (firstTime D hI)) z‖) ≤ _
      simp_rw [norm_mul]
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hn : ∀ v, u v ≤ 0 := fun v => (hu.2.1 v).le
      exact integral_norm_exponentialBox_le_all (lowerTimeExit_nonneg D hI u hn) (hn (firstTime D hI))
    _ = _ := by rw [integral_mul_const,mul_comm]

end WaveTurbulence.SumintPar
