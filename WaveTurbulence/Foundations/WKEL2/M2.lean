/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.RadialSphereIntegral

/-!
# The uniform M₂ bound

Research-note Lemma 4(a), throughout `d ≥ 3`, `2s > d-2`.
-/

public section

noncomputable section

open MeasureTheory Metric
open scoped InnerProductSpace ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

attribute [local instance] referenceMeasureSpace referenceBorelSpace

/-- Uniform M₂ bound, including integrability on each great sphere.
The single constant depends on `d,s` and not on the center or the hyperplane. -/
theorem exists_uniform_M2 (hd : 3 ≤ d) (s : ℝ) (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : Mom d, ℓ ≠ 0 → ∀ k : Mom d,
      Integrable (fun θ : sphere (0 : ↥(ℝ ∙ ℓ)ᗮ) 1 => radialWeight d s k θ.1)
        (volume : Measure ↥(ℝ ∙ ℓ)ᗮ).toSphere ∧
      (∫ θ : sphere (0 : ↥(ℝ ∙ ℓ)ᗮ) 1, radialWeight d s k θ.1
        ∂(volume : Measure ↥(ℝ ∙ ℓ)ᗮ).toSphere) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_hyperplane_inverse hd (2 * s)
    (by linarith only [hs])
  refine ⟨C, hC, fun ℓ hℓ k => ?_⟩
  obtain ⟨hiH, hbH⟩ := hbound ℓ hℓ k
  obtain ⟨hiA, heA⟩ := integrable_radialWeight_sphere_eq_of_integrable hd s hs ℓ hℓ k hiH
  exact ⟨hiA, heA.le.trans hbH⟩

end WaveTurbulence.WKEL2
