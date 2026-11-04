/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.OrderedCoordinates
public import WaveTurbulence.Foundations.Fourier.CoordinateCutoff
import Mathlib.Tactic

/-!
# Compactly supported ordered time integrals

The output cutoffs alone give compact support. Smooth amplitudes give
smooth output, irrespective of oscillatory parameters in the amplitude.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- Ordered integration with a scalar cutoff at each output time. -/
@[expose] noncomputable def cutoffOrderedIntegral (n : ℕ) (χ : ℝ → ℝ)
    (A : (Fin n → ℝ) → ℂ) (t : Fin 2 → ℝ) : ℂ :=
  coordinateCutoff χ t * orderedIntegral n A (t 0) (t 1)

/-- Smoothness of the cutoff ordered integral for every number of integration variables. -/
theorem cutoffOrderedIntegral_contDiff {n : ℕ} {χ : ℝ → ℝ} {A : (Fin n → ℝ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (cutoffOrderedIntegral n χ A) := by
  apply (coordinateCutoff_contDiff hχ).mul
  exact contDiff_orderedIntegral n (hA.comp contDiff_snd) (by fun_prop) (by fun_prop)

/-- Compact output support, with no assumption on the amplitude. -/
theorem cutoffOrderedIntegral_hasCompactSupport {n : ℕ} {χ : ℝ → ℝ}
    (hc : HasCompactSupport χ) (A : (Fin n → ℝ) → ℂ) :
    HasCompactSupport (cutoffOrderedIntegral n χ A) :=
  (coordinateCutoff_hasCompactSupport hc).mul_right

/-- Every smooth amplitude gives an integrable time slice after the output cutoffs. -/
theorem cutoffOrderedIntegral_integrable {n : ℕ} {χ : ℝ → ℝ} {A : (Fin n → ℝ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hA : ContDiff ℝ ∞ A) :
    Integrable (cutoffOrderedIntegral n χ A) :=
  (cutoffOrderedIntegral_contDiff hχ hA).continuous.integrable_of_hasCompactSupport
    (cutoffOrderedIntegral_hasCompactSupport hc A)

end WaveTurbulence.Fourier
