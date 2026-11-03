/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Nonnegative scalar change of variables for the two-direction Jacobian
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

/-- Positive scalar dilation and translation, valid also for infinite integrals. -/
theorem lintegral_scalar_affine {G : ℝ → ℝ≥0∞} (hG : Measurable G)
    (c σ : ℝ) (hσ : 0 < σ) :
    (∫⁻ u : ℝ, G (c + σ * u)) = ENNReal.ofReal (σ⁻¹) * ∫⁻ t : ℝ, G t := by
  have hm : Measurable (fun t : ℝ => G (c + t)) :=
    hG.comp (continuous_const.add continuous_id).measurable
  calc
    _ = ∫⁻ t : ℝ, G (c + t) ∂Measure.map (fun u : ℝ => σ • u) volume := by
      have hD : Measurable (fun u : ℝ => σ • u) := by fun_prop
      simpa only [smul_eq_mul] using (lintegral_map hm hD).symm
    _ = ENNReal.ofReal (σ⁻¹) * ∫⁻ t : ℝ, G (c + t) := by
      rw [Measure.map_addHaar_smul volume hσ.ne', lintegral_smul_measure]
      simp only [CommSemiring.finrank_self, pow_one, abs_of_pos (inv_pos.mpr hσ), smul_eq_mul]
    _ = _ := by rw [lintegral_add_left_eq_self G c]

/-- A triangular scalar shear separates two nonnegative ray factors. -/
theorem lintegral_scalar_shear_product {F G : ℝ → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) (c σ : ℝ) (hσ : 0 < σ) :
    (∫⁻ t : ℝ, ∫⁻ u : ℝ, F t * G (c * t + σ * u)) =
      ENNReal.ofReal (σ⁻¹) * (∫⁻ t : ℝ, F t) * ∫⁻ u : ℝ, G u := by
  have hinner (t : ℝ) : (∫⁻ u : ℝ, F t * G (c * t + σ * u)) =
      F t * (ENNReal.ofReal (σ⁻¹) * ∫⁻ u : ℝ, G u) := by
    have hm : Measurable (fun u : ℝ => G (c * t + σ * u)) := hG.comp (by fun_prop)
    rw [lintegral_const_mul _ hm, lintegral_scalar_affine hG (c * t) σ hσ]
  simp_rw [hinner]
  rw [lintegral_mul_const _ hF]
  ac_rfl

end WaveTurbulence.WKEL2
