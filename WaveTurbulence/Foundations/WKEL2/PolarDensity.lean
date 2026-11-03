/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.PolarRadial

/-!
# Expanding the radial polar density on the positive ray
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.WKEL2

/-- Expand the radial measure into its power density and ordinary Lebesgue measure. -/
theorem lintegral_volumeIoiPow_comp (n : ℕ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ r : Ioi (0 : ℝ), F r.1 ∂Measure.volumeIoiPow n) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) * F r := by
  have hp : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ n)) :=
    (measurable_subtype_coe.pow_const n).ennreal_ofReal
  have hc : Measurable (fun r : Ioi (0 : ℝ) => F r.1) := hF.comp measurable_subtype_coe
  have h := lintegral_withDensity_eq_lintegral_mul
    ((volume : Measure ℝ).comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) hp hc
  exact h.trans (lintegral_subtype_comap measurableSet_Ioi
    (fun r => ENNReal.ofReal (r ^ n) * F r))

end WaveTurbulence.WKEL2
