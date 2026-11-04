/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FourierMixture

/-! # Pointwise integrability of an amplitude times a uniformly bounded kernel -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Conditional integrability transport using a finite pointwise kernel envelope. -/
theorem integrable_mul_of_uniform_enorm_bound {U : Type*} [MeasurableSpace U]
    (μ : Measure U) (A K : U → ℂ) (hA : Integrable A μ) (hK : AEStronglyMeasurable K μ)
    {N : ℝ≥0∞} (hN : N < ⊤) (hb : ∀ u, ‖K u‖ₑ ≤ N) :
    Integrable (fun u => A u * K u) μ := by
  apply hA.mul_bdd hK
  apply ae_of_all
  intro u
  simpa only [toReal_enorm] using ENNReal.toReal_mono hN.ne (hb u)

end WaveTurbulence.Incoh
