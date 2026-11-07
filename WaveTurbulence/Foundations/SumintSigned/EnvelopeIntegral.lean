/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Weighted integration of a pointwise envelope bound

This is the nonnegative Tonelli core of the mixed Fourier Minkowski
estimate. Keeping its coefficient functions abstract avoids unfolding
Fourier transforms during unification of integral identities.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintSigned

/-- Integrate a common pointwise envelope majorant and interchange the
parameter and frequency integrals. -/
theorem lintegral_weighted_envelope_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] (w : β → ℝ≥0∞) (E : α → β → ℝ≥0∞) (G : β → ℝ≥0∞)
    (hw : Measurable w) (hE : Measurable (Function.uncurry E))
    (hG : ∀ b, G b ≤ ∫⁻ a, E a b ∂μ) :
    (∫⁻ b, w b*G b ∂ν) ≤ ∫⁻ a, (∫⁻ b, w b*E a b ∂ν) ∂μ := by
  have hEb (b : β) : Measurable (fun a => E a b) :=
    hE.comp (measurable_id.prodMk measurable_const)
  have hW : Measurable (Function.uncurry (fun a b => w b*E a b)) :=
    (hw.comp measurable_snd).mul hE
  calc
    _ ≤ ∫⁻ b, w b*(∫⁻ a, E a b ∂μ) ∂ν :=
      lintegral_mono (fun b => mul_le_mul' le_rfl (hG b))
    _ = ∫⁻ b, (∫⁻ a, w b*E a b ∂μ) ∂ν := by
      apply lintegral_congr
      intro b
      exact (lintegral_const_mul _ (hEb b)).symm
    _ = _ := (lintegral_lintegral_swap hW.aemeasurable).symm

end WaveTurbulence.SumintSigned
