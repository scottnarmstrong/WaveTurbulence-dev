/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.HyperplaneRadialIdentity
public import WaveTurbulence.Foundations.WKEL2.NonnegativeIntegral

/-!
# Converting the nonnegative M₂ identity to Bochner integration
-/

public section

noncomputable section

open MeasureTheory Metric
open scoped InnerProductSpace ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Measurable ambient inclusion of a great sphere. -/
theorem measurable_greatSphere_inclusion (ℓ : Mom d) :
    Measurable (fun θ : sphere (0 : ↥(ℝ ∙ ℓ)ᗮ) 1 => (θ.1 : Mom d)) :=
  (continuous_subtype_val.comp continuous_subtype_val).measurable

/-- Measurability of the radial weight on a fixed great sphere. -/
theorem measurable_radialWeight_sphere (s : ℝ) (ℓ k : Mom d) :
    Measurable (fun θ : sphere (0 : ↥(ℝ ∙ ℓ)ᗮ) 1 => radialWeight d s k θ.1) := by
  have hb : Continuous (fun q : sphere (0 : ↥(ℝ ∙ ℓ)ᗮ) 1 × ℝ =>
      1 + ‖k + q.2 • (q.1.1 : Mom d)‖ ^ 2) := by fun_prop
  have hc : Continuous (fun q : sphere (0 : ↥(ℝ ∙ ℓ)ᗮ) 1 × ℝ =>
      (1 + ‖k + q.2 • (q.1.1 : Mom d)‖ ^ 2) ^ (-s) * q.2 ^ (d - 3)) :=
    (hb.rpow_const (fun _ => Or.inl (by positivity))).mul (continuous_snd.pow _)
  exact hc.stronglyMeasurable.integral_prod_right.measurable

/-- Nonnegative mass identity when the hyperplane convolution is integrable. -/
theorem lintegral_radialWeight_sphere_eq_of_integrable (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (ℓ : Mom d) (hℓ : ℓ ≠ 0) (k : Mom d)
    (hi : Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ =>
      japaneseDecay (2 * s) (k + (w : Mom d)) * ‖(w : Mom d)‖⁻¹)) :
    (∫⁻ θ : sphere (0 : ↥(ℝ ∙ ℓ)ᗮ) 1, ENNReal.ofReal (radialWeight d s k θ.1)
      ∂(volume : Measure ↥(ℝ ∙ ℓ)ᗮ).toSphere) =
      ENNReal.ofReal (∫ w : ↥(ℝ ∙ ℓ)ᗮ,
        japaneseDecay (2 * s) (k + (w : Mom d)) * ‖(w : Mom d)‖⁻¹) := by
  have hn (w : ↥(ℝ ∙ ℓ)ᗮ) :
      0 ≤ japaneseDecay (2 * s) (k + (w : Mom d)) * ‖(w : Mom d)‖⁻¹ :=
    mul_nonneg (japaneseDecay_nonneg _ _) (inv_nonneg.mpr (norm_nonneg _))
  exact ((ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)).trans
    (lintegral_hyperplane_inverse_eq_radialWeight hd s hs ℓ hℓ k)).symm

/-- Integrability and exact integral on a great sphere, from the spatial integral. -/
theorem integrable_radialWeight_sphere_eq_of_integrable (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (ℓ : Mom d) (hℓ : ℓ ≠ 0) (k : Mom d)
    (hi : Integrable (fun w : ↥(ℝ ∙ ℓ)ᗮ =>
      japaneseDecay (2 * s) (k + (w : Mom d)) * ‖(w : Mom d)‖⁻¹)) :
    Integrable (fun θ : sphere (0 : ↥(ℝ ∙ ℓ)ᗮ) 1 => radialWeight d s k θ.1)
        (volume : Measure ↥(ℝ ∙ ℓ)ᗮ).toSphere ∧
      (∫ θ : sphere (0 : ↥(ℝ ∙ ℓ)ᗮ) 1, radialWeight d s k θ.1
        ∂(volume : Measure ↥(ℝ ∙ ℓ)ᗮ).toSphere) =
        ∫ w : ↥(ℝ ∙ ℓ)ᗮ, japaneseDecay (2 * s) (k + (w : Mom d)) * ‖(w : Mom d)‖⁻¹ := by
  apply integrable_integral_eq_of_lintegral_ofReal_eq
    (measurable_radialWeight_sphere s ℓ k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ => radialWeight_nonneg _ _ _ _)
  · exact integral_nonneg fun _ =>
      mul_nonneg (japaneseDecay_nonneg _ _) (inv_nonneg.mpr (norm_nonneg _))
  · exact lintegral_radialWeight_sphere_eq_of_integrable hd s hs ℓ hℓ k hi

end WaveTurbulence.WKEL2
