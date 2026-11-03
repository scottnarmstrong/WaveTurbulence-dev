/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.Polar

/-!
# The inverse-radius factor in resonant polar coordinates

Multiplication by `r⁻¹` lowers the radial density exponent by one.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.WKEL2

/-- The inverse radius lowers a positive-ray power density by one. -/
theorem volumeIoiPow_withDensity_inv (n : ℕ) :
    (Measure.volumeIoiPow (n + 1)).withDensity
      (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1⁻¹)) = Measure.volumeIoiPow n := by
  have hp : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ (n + 1))) :=
    (measurable_subtype_coe.pow_const _).ennreal_ofReal
  have hi : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1⁻¹)) :=
    measurable_subtype_coe.inv.ennreal_ofReal
  rw [Measure.volumeIoiPow, Measure.volumeIoiPow,
    ← withDensity_mul ((volume : Measure ℝ).comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) hp hi]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    dsimp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (pow_nonneg r.2.le _), pow_succ, mul_assoc,
      mul_inv_cancel₀ r.2.ne', mul_one]

/-- Integral version of lowering the radial exponent, including infinite values. -/
theorem lintegral_volumeIoiPow_inv (n : ℕ) {G : Ioi (0 : ℝ) → ℝ≥0∞}
    (hG : Measurable G) :
    (∫⁻ r, ENNReal.ofReal (r.1⁻¹) * G r ∂Measure.volumeIoiPow (n + 1)) =
      ∫⁻ r, G r ∂Measure.volumeIoiPow n := by
  have hi : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1⁻¹)) :=
    measurable_subtype_coe.inv.ennreal_ofReal
  calc
    _ = ∫⁻ r, G r ∂(Measure.volumeIoiPow (n + 1)).withDensity
        (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1⁻¹)) :=
      (lintegral_withDensity_eq_lintegral_mul _ hi hG).symm
    _ = _ := by rw [volumeIoiPow_withDensity_inv]

end WaveTurbulence.WKEL2
