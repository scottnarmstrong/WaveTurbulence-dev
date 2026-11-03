/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.HyperplaneInverseBound
public import WaveTurbulence.Foundations.WKEL2.PolarDensity

/-!
# The M₂ sphere integral as an inverse-norm hyperplane integral
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped InnerProductSpace ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Nonnegative identity behind Lemma 4(a), including potentially infinite outer integrals. -/
theorem lintegral_hyperplane_inverse_eq_radialWeight (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (ℓ : Mom d) (hℓ : ℓ ≠ 0) (k : Mom d) :
    (∫⁻ w : ↥(ℝ ∙ ℓ)ᗮ, ENNReal.ofReal (japaneseDecay (2 * s) (k + (w : Mom d)) * ‖(w : Mom d)‖⁻¹)) =
      ∫⁻ θ : sphere (0 : ↥(ℝ ∙ ℓ)ᗮ) 1, ENNReal.ofReal (radialWeight d s k θ.1)
        ∂(volume : Measure ↥(ℝ ∙ ℓ)ᗮ).toSphere := by
  have : Nontrivial ↥(ℝ ∙ ℓ)ᗮ := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_perp hℓ]; omega)
  have hJ : Continuous (fun w : ↥(ℝ ∙ ℓ)ᗮ => japaneseDecay (2 * s) (k + (w : Mom d))) := by
    have hb : Continuous (fun w : ↥(ℝ ∙ ℓ)ᗮ => 1 + ‖k + (w : Mom d)‖ ^ 2) := by fun_prop
    exact hb.rpow_const (fun _ => Or.inl (by positivity))
  have hH : Measurable (fun w : ↥(ℝ ∙ ℓ)ᗮ =>
      ENNReal.ofReal (japaneseDecay (2 * s) (k + (w : Mom d)) * ‖(w : Mom d)‖⁻¹)) :=
    (hJ.measurable.mul (measurable_norm.comp measurable_subtype_coe).inv).ennreal_ofReal
  rw [lintegral_polar (volume : Measure ↥(ℝ ∙ ℓ)ᗮ) hH]
  apply lintegral_congr
  intro θ
  have hθ : ‖(θ.1 : Mom d)‖ = 1 := mem_sphere_zero_iff_norm.mp θ.2
  have hFr : Measurable (fun ρ : ℝ => ENNReal.ofReal
      (japaneseDecay (2 * s) (k + ρ • (θ.1 : Mom d)))) := by
    have hb : Continuous (fun ρ : ℝ => 1 + ‖k + ρ • (θ.1 : Mom d)‖ ^ 2) := by fun_prop
    exact (hb.rpow_const (fun _ => Or.inl (by positivity))).measurable.ennreal_ofReal
  have hrewrite : (fun ρ : Ioi (0 : ℝ) => ENNReal.ofReal
      (japaneseDecay (2 * s) (k + ((ρ.1 • θ.1 : ↥(ℝ ∙ ℓ)ᗮ) : Mom d)) *
        ‖((ρ.1 • θ.1 : ↥(ℝ ∙ ℓ)ᗮ) : Mom d)‖⁻¹)) =
      (fun ρ : Ioi (0 : ℝ) => ENNReal.ofReal (ρ.1⁻¹) *
        ENNReal.ofReal (japaneseDecay (2 * s) (k + ρ.1 • (θ.1 : Mom d)))) := by
    funext ρ
    simp only [Submodule.coe_smul, norm_smul, Real.norm_of_nonneg ρ.2.le, hθ, mul_one]
    rw [ENNReal.ofReal_mul (japaneseDecay_nonneg _ _)]
    exact mul_comm _ _
  have hG : Measurable (fun ρ : Ioi (0 : ℝ) => ENNReal.ofReal
      (japaneseDecay (2 * s) (k + ρ.1 • (θ.1 : Mom d)))) := hFr.comp measurable_subtype_coe
  rw [hrewrite, finrank_perp hℓ,
    show d - 1 - 1 = (d - 3) + 1 by omega,
    lintegral_volumeIoiPow_inv (d - 3) hG,
    lintegral_volumeIoiPow_comp (d - 3) hFr]
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun ρ => (1 + ‖k + ρ • (θ.1 : Mom d)‖ ^ 2) ^ (-s) * ρ ^ (d - 3)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (pow_nonneg hρ.le _)
  have hi := ofReal_integral_eq_lintegral_ofReal (integrable_radialWeight hd s hs k θ.1 hθ) hn
  rw [radialWeight, hi]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
  rw [japaneseDecay, show -(2 * s) / 2 = -s by ring,
    ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
  exact mul_comm _ _

end WaveTurbulence.WKEL2
