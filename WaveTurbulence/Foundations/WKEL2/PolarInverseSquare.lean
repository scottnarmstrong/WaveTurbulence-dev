/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.PolarRadial

/-!
# Lowering polar density by two inverse-radius factors
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.WKEL2

/-- Two inverse radii lower the radial density exponent by two. -/
theorem lintegral_volumeIoiPow_inv_sq (n : ℕ) {G : Ioi (0 : ℝ) → ℝ≥0∞}
    (hG : Measurable G) :
    (∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (r.1⁻¹) * ENNReal.ofReal (r.1⁻¹) * G r
      ∂Measure.volumeIoiPow (n + 2)) = ∫⁻ r, G r ∂Measure.volumeIoiPow n := by
  have hIG : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1⁻¹) * G r) :=
    measurable_subtype_coe.inv.ennreal_ofReal.mul hG
  simp only [mul_assoc]
  rw [show n + 2 = (n + 1) + 1 by omega, lintegral_volumeIoiPow_inv (n + 1) hIG,
    lintegral_volumeIoiPow_inv n hG]

end WaveTurbulence.WKEL2
