/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootDensityL1
public import WaveTurbulence.Foundations.Fourier.TimeIntegralBounds
public import WaveTurbulence.Foundations.Fourier.Norm00V

/-!
# Negative regularity of the actual causal tree extension

TARGET (incohproof25)–(incohproof26). The root marginal is formed from the
literal normalized product over its actual measurable time-order domain.
The momentum supremum stays inside the Fourier integral.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- The causal cutoff extension of the actual root/lone-parent marginal. -/
@[expose] def RootCoordinates.treeCausalExtension {d n : ℕ} (R : RootCoordinates n)
    (χ : ℝ → ℝ) (L γ δ : ℝ) (Q : Mom d → Fin n → LayerLink d)
    (I : Mom d → Set (Fin n → Fin 2 → ℝ)) : (Fin 2 → ℝ) → Mom d → ℂ :=
  Fourier.cutoffJ χ (fun t k => R.linkDensity L γ δ (Q k) (I k) t)

end WaveTurbulence.Incoh
