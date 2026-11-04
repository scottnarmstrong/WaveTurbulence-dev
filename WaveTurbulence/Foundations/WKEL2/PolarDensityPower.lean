/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.PolarDensity

/-!
# Raising the radial density by a nonnegative integral power
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.WKEL2

/-- Multiplication by `r^m` raises the radial density exponent by `m`. -/
theorem volumeIoiPow_withDensity_pow (n m : ℕ) :
    (Measure.volumeIoiPow n).withDensity
      (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ m)) = Measure.volumeIoiPow (n + m) := by
  have hn : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ n)) :=
    (measurable_subtype_coe.pow_const n).ennreal_ofReal
  have hm : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ m)) :=
    (measurable_subtype_coe.pow_const m).ennreal_ofReal
  rw [Measure.volumeIoiPow, Measure.volumeIoiPow, ← withDensity_mul _ hn hm]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    dsimp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (pow_nonneg r.2.le _), ← pow_add]

/-- Integral form of increasing the radial density exponent. -/
theorem lintegral_volumeIoiPow_pow (n m : ℕ) {G : Ioi (0 : ℝ) → ℝ≥0∞}
    (hG : Measurable G) :
    (∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (r.1 ^ m) * G r ∂Measure.volumeIoiPow n) =
      ∫⁻ r, G r ∂Measure.volumeIoiPow (n + m) := by
  have hm : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ m)) :=
    (measurable_subtype_coe.pow_const m).ennreal_ofReal
  calc
    _ = ∫⁻ r, G r ∂(Measure.volumeIoiPow n).withDensity
        (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ m)) :=
      (lintegral_withDensity_eq_lintegral_mul _ hm hG).symm
    _ = _ := by rw [volumeIoiPow_withDensity_pow]

end WaveTurbulence.WKEL2
