/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!+# Nonnegative polar integration

The polar-coordinate ingredient for Corollary 2 of
`docs/research/git20-general-d.md`. This formulation applies both to momentum
space and to a fixed hyperplane, with the radial density kept in the measure.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Polar integration of a nonnegative Borel function against Haar measure.
The sphere measure is `μ.toSphere`, and the radial measure has density
`r^(finrank ℝ E - 1)` on the positive ray. -/
theorem lintegral_polar (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : E → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂μ =
      ∫⁻ θ : sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ), F (r.1 • θ.1)
        ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) ∂μ.toSphere := by
  let H : sphere (0 : E) 1 × Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun p => F (p.2.1 • p.1.1)
  have hH : Measurable H := hF.comp
    ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).measurable
  calc
    ∫⁻ x, F x ∂μ = ∫⁻ x : ({(0 : E)}ᶜ : Set E), F x.1 ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = ∫⁻ p, H p ∂μ.toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      have hp := μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp hH
      simpa only [H, ← homeomorphUnitSphereProd_symm_apply_coe,
        Homeomorph.symm_apply_apply] using hp
    _ = _ := lintegral_prod H hH.aemeasurable

end WaveTurbulence.WKEL2
