/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.Reduction

/-!
# The explicit data-mass gauge formula for the NLS bridge

TARGET (reducedcoef), L540–L566. This exposes the landed reduced coefficient
using only the initial Fourier coefficients and the physical time scale.
-/

public section

noncomputable section

open Set

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-- The landed gauge equals the source formula with the initial coefficient mass. -/
theorem bridge_reducedCoeff_eq {L α γ δ T : ℝ} {c : (Fin d → ℤ) → ℂ}
    {u : ℝ → (Fin d → ℝ) → ℂ} (hL : 0 < L) (hT : 0 ≤ T)
    (hα : α = L ^ (-γ)) (hu : IsSmoothNLSSolution L α T c u) :
    reducedCoeff L γ δ u = fun t n =>
      Complex.exp (-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t : ℝ) * Complex.I) *
      Complex.exp (-(2 * α * ((L ^ d)⁻¹ * ∑' n, ‖c n‖ ^ 2) * δ * kineticTime α * t : ℝ) * Complex.I) *
      torusFourierCoeff L (u (δ * kineticTime α * t)) n := by
  subst α
  funext t n
  rw [reducedCoeff, torusFourierCoeff_wickGauge, hu.massAvg_eq hL ⟨le_rfl, hT⟩]
  have H : -2 * L ^ (-γ) * ((L ^ d)⁻¹ * ∑' n, ‖c n‖ ^ 2) * (δ * kineticTime (L ^ (-γ)) * t) =
      -(2 * L ^ (-γ) * ((L ^ d)⁻¹ * ∑' n, ‖c n‖ ^ 2) * δ * kineticTime (L ^ (-γ)) * t) := by ring
  rw [H]
  simp only [Complex.ofReal_neg, mul_assoc]

end WaveTurbulence.NLS
