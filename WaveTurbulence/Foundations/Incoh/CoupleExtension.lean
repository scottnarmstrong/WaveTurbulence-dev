/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LocalRootDensity
public import WaveTurbulence.Foundations.Incoh.LinkCounting
public import WaveTurbulence.Foundations.Fourier.TimeIntegralBounds

/-!
# The positive Fourier bound for the actual couple density

TARGET (incohproof17)–(incohproof20). Form the cutoff double integral of
the actual local-clock root marginal, translate back to physical clocks,
and apply the landed time-integration theorem. No endpoint estimate is assumed.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- The canonical cutoff double integral in the original root clocks. -/
@[expose] def RootCoordinates.coupleExtension {d n : ℕ} (R : RootCoordinates n)
    (χ : ℝ → ℝ) (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (t : Fin 2 → ℝ) : ℂ :=
  Fourier.cutoffDoubleIntegral χ (R.localLinkDensity L γ δ Q I) (t - R.baseRootTimes Q)

/-- Returning from local clocks preserves the weighted Fourier norm exactly. -/
theorem RootCoordinates.timeFourierNorm_coupleExtension {d n : ℕ} (R : RootCoordinates n)
    (χ : ℝ → ℝ) (L γ δ θ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ)) :
    Fourier.timeFourierNorm θ (R.coupleExtension χ L γ δ Q I) =
      Fourier.timeFourierNorm θ (Fourier.cutoffDoubleIntegral χ (R.localLinkDensity L γ δ Q I)) := by
  have heq : R.coupleExtension χ L γ δ Q I =
      fun t => Fourier.cutoffDoubleIntegral χ (R.localLinkDensity L γ δ Q I) (t + -(R.baseRootTimes Q)) := by
    funext t
    rw [coupleExtension, sub_eq_add_neg]
  rw [heq, Fourier.timeFourierNorm_translate]

end WaveTurbulence.Incoh
