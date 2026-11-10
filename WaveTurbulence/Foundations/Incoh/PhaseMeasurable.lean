/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.OrderedIntegralMeasurable
public import WaveTurbulence.Foundations.Fourier.BalancedPhase
public import WaveTurbulence.Foundations.Fourier.CoordinateCutoffDerivative
public import WaveTurbulence.Foundations.Fourier.DirectionalFourierMoments
public import WaveTurbulence.Foundations.Fourier.WeightedOrderedIntegral

/-!
# Measurable phase amplitudes and cutoff ordered kernels

Arbitrary measurable dependence on internal clocks is compatible with
literal ordered integration and the universal phase envelope.
-/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- Measurable amplitudes and output clocks give measurable cutoff ordered kernels. -/
theorem stronglyMeasurable_weightedOrderedIntegral_comp {Z : Type*} [MeasurableSpace Z]
    {m : ℕ} {χ : ℝ → ℝ} (hχ : Measurable χ)
    {F : Z × (Fin m → ℝ) → ℂ} (hF : StronglyMeasurable F)
    {t : Z → Fin 2 → ℝ} (ht : Measurable t) :
    StronglyMeasurable (fun z => Fourier.weightedOrderedIntegral m χ χ (fun v => F (z, v)) (t z)) := by
  have hc (j : Fin 2) : StronglyMeasurable (fun z => (χ (t z j) : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp (hχ.comp ((measurable_pi_apply j).comp ht))).stronglyMeasurable
  exact ((hc 0).mul (hc 1)).mul (stronglyMeasurable_orderedIntegral m hF
    ((measurable_pi_apply 1).comp ht) ((measurable_pi_apply 0).comp ht))

end WaveTurbulence.Incoh
