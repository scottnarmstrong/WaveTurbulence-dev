/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.IntegralFourierL2
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Fourier endpoints for Hausdorff–Young

The endpoint estimates for TARGET L2370 use the `exp(-2π i ⟨x,ξ⟩)`
normalization. Both endpoint constants are exactly one.
-/

public section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace WaveTurbulence.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The `L¹ → L∞` endpoint of TARGET's Hausdorff–Young estimate (L2370). -/
theorem integral_fourier_eLpNorm_top_le {f : V → ℂ} (hf : Integrable f) :
    eLpNorm (𝓕 f) ∞ ≤ eLpNorm f 1 := by
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (L := innerₗ V) continuous_inner hf
  rw [eLpNorm_exponent_top hc.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hf]
  exact eLpNormEssSup_le_of_ae_bound
    (ae_of_all _ fun ξ => Real.norm_fourier_le_integral_norm f ξ)

end WaveTurbulence.Fourier
