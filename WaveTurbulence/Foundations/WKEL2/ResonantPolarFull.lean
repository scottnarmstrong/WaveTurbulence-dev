/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.ResonantPolar

/-!
# Polar coordinates in both resonant variables

Corollary 2 of `docs/research/git20-general-d.md`, in fixed hyperplane coordinates.
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Double polar formula for resonant measure. Both radial densities are
`r^(d-2)`, as in research-note Corollary 2. -/
theorem lintegral_resonantMeasure_polar {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {F : Mom d × Mom d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂resonantMeasure e =
      ∫⁻ φ : sphere (0 : Mom d) 1,
        ∫⁻ ρ : Ioi (0 : ℝ),
          ∫⁻ θ : sphere (0 : ↥(ℝ ∙ e)ᗮ) 1,
            ∫⁻ r : Ioi (0 : ℝ), F (ρ.1 • φ.1, r.1 • normalReflection e φ.1 θ.1)
              ∂Measure.volumeIoiPow (d - 2)
            ∂(volume : Measure ↥(ℝ ∙ e)ᗮ).toSphere
          ∂Measure.volumeIoiPow (d - 2)
        ∂(volume : Measure (Mom d)).toSphere := by
  have he0 : e ≠ 0 := by intro h; simp only [h, norm_zero, zero_ne_one] at he
  have : Nontrivial ↥(ℝ ∙ e)ᗮ := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_perp he0]; omega)
  rw [lintegral_resonantMeasure_polar_left e hd hF]
  apply lintegral_congr
  intro φ
  apply lintegral_congr
  intro ρ
  have hG : Measurable (fun w : ↥(ℝ ∙ e)ᗮ => F (ρ.1 • φ.1, normalReflection e φ.1 w)) :=
    hF.comp (continuous_const.prodMk
      ((normalReflection e φ.1).continuous.comp continuous_subtype_val)).measurable
  have hp := lintegral_polar (volume : Measure ↥(ℝ ∙ e)ᗮ) hG
  simpa only [finrank_perp he0, show d - 1 - 1 = d - 2 by omega,
    Submodule.coe_smul, map_smul] using hp

end WaveTurbulence.WKEL2
