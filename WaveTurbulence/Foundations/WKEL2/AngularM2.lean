/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.M2
public import WaveTurbulence.Foundations.WKEL2.AngularCoordinates
public import WaveTurbulence.Foundations.WKEL2.SphereMeasureIsometry

/-!
# The M₂ bound in the fixed angular coordinates
-/

public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- The M₂ disintegration bound in any fixed reference hyperplane's sphere. -/
theorem exists_uniform_reference_M2 (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : Mom d, ‖e‖ = 1 → ∀ φ : Mom d, ‖φ‖ = 1 → ∀ k : Mom d,
      (∫⁻ θ : sphere (0 : ↥(ℝ ∙ e)ᗮ) 1,
        ENNReal.ofReal (radialWeight d s k (normalReflection e φ θ.1))
          ∂(volume : Measure ↥(ℝ ∙ e)ᗮ).toSphere) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_M2 hd s hs
  refine ⟨C, hC, fun e he φ hφ k => ?_⟩
  have hφ0 : φ ≠ 0 := by intro h; simp only [h, norm_zero, zero_ne_one] at hφ
  obtain ⟨hiA, hbA⟩ := hbound φ hφ0 k
  let T := hyperplaneChart he hφ0
  let S := unitSphereEquiv T
  have hMP := measurePreserving_unitSphereEquiv T
  have heq :
      (∫⁻ θ : sphere (0 : ↥(ℝ ∙ e)ᗮ) 1,
        ENNReal.ofReal (radialWeight d s k (normalReflection e φ θ.1))
          ∂(volume : Measure ↥(ℝ ∙ e)ᗮ).toSphere) =
        ∫⁻ θ : sphere (0 : ↥(ℝ ∙ φ)ᗮ) 1, ENNReal.ofReal (radialWeight d s k θ.1)
          ∂(volume : Measure ↥(ℝ ∙ φ)ᗮ).toSphere := by
    have h := hMP.lintegral_comp_emb S.measurableEmbedding
      (fun θ : sphere (0 : ↥(ℝ ∙ φ)ᗮ) 1 => ENNReal.ofReal (radialWeight d s k θ.1))
    simpa only [T, S, coe_unitSphereEquiv, coe_hyperplaneChart] using h
  have hn : 0 ≤ᵐ[(volume : Measure ↥(ℝ ∙ φ)ᗮ).toSphere]
      (fun θ : sphere (0 : ↥(ℝ ∙ φ)ᗮ) 1 => radialWeight d s k θ.1) :=
    Filter.Eventually.of_forall fun _ => radialWeight_nonneg _ _ _ _
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal hiA hn]
  exact ENNReal.ofReal_le_ofReal hbA

end WaveTurbulence.WKEL2
