/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.PrincipalValueSlices
public import WaveTurbulence.Foundations.Resonant.SliceRegularity

/-!
# Existence of the principal value of the inverse energy resonance

For a continuously differentiable kernel with an integrable polynomial decay
profile for its gradient and a uniform support radius in the second momentum,
the cutoff limit for `1/(-2⟨ℓ,x⟩)` exists. Both finite iterated integrals are
honest Bochner integrals. This provides existence in the parametrization of
the frozen collision operator; it does not assert frequency-uniform estimates.
-/

public section

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace NNReal

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- Finite cutoff integral of the inverse energy resonance. -/
@[expose] noncomputable def energyInvIntegral (χ : ℝ → ℝ) (μ : ℝ)
    (F : Mom d → Mom d → ℝ) : ℝ := ∫ ℓ, energyInvInner χ μ F ℓ

/-- Absolutely convergent symmetric-quotient representation of the slice limit. -/
@[expose] noncomputable def energyInvSliceLimit (F : Mom d → Mom d → ℝ) (ℓ : Mom d) : ℝ :=
  -(2 * ‖ℓ‖)⁻¹ * ∫ t, pvQuotient (sliceInt F ℓ) t

theorem stronglyMeasurable_energyInvInner
    {F : Mom d → Mom d → ℝ} {A : Mom d → ℝ} {a : Mom d → Mom d} {N : ℝ}
    (hF : DeltaKernel F A a N) {χ : ℝ → ℝ} (hχ : IsPVCutoff χ) (μ : ℝ) :
    StronglyMeasurable (energyInvInner χ μ F) := by
  apply StronglyMeasurable.integral_prod_right
  apply Continuous.stronglyMeasurable
  exact hF.cont.mul ((hχ.continuous_div μ).comp
    ((continuous_const.mul (continuous_fst.inner continuous_snd)).neg))

end WaveTurbulence.Resonant
