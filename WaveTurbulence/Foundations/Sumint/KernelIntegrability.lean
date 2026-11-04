/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability through kernels of uniformly bounded absolute mass

This auxiliary criterion supplies the genuine ambient integrability guard
before the explicit extension is Fourier transformed.
-/

public section

open MeasureTheory

namespace WaveTurbulence.Sumint

/-- An integrable coefficient times a measurable kernel of uniformly bounded
absolute mass is integrable on the product space. -/
theorem integrable_mul_kernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (f : α → ℂ) (K : α → β → ℂ) (hf : Integrable f μ)
    (hm : AEStronglyMeasurable (fun p : α × β => f p.1 * K p.1 p.2) (μ.prod ν))
    (hK : ∀ᵐ x ∂μ, Integrable (K x) ν) {C : ℝ}
    (hb : ∀ᵐ x ∂μ, (∫ y, ‖K x y‖ ∂ν) ≤ C) :
    Integrable (fun p : α × β => f p.1 * K p.1 p.2) (μ.prod ν) := by
  apply (integrable_prod_iff hm).mpr
  refine ⟨?_, ?_⟩
  · filter_upwards [hK] with x hx
    change Integrable (fun y => f x * K x y) ν
    exact hx.const_mul (f x)
  ·
    have he (x : α) : (∫ y, ‖f x * K x y‖ ∂ν) = ‖f x‖ * ∫ y, ‖K x y‖ ∂ν := by
      simp_rw [norm_mul]
      exact integral_const_mul _ _
    simp_rw [he]
    apply (hf.norm.mul_const C).mono'
    · have hh := hm.norm.integral_prod_right'
      change AEStronglyMeasurable (fun x => ∫ y, ‖f x * K x y‖ ∂ν) μ at hh
      simpa only [he] using hh
    · filter_upwards [hb] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (integral_nonneg (fun _ => norm_nonneg _)))]
      exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)

end WaveTurbulence.Sumint
