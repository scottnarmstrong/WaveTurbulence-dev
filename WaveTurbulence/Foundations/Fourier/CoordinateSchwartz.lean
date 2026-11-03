/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.Periodization
public import WaveTurbulence.Foundations.Fourier.TimeEuclidean
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Schwartz Fourier transforms in product coordinates

Changing from the Euclidean norm to the coordinate sup norm preserves the
Schwartz class. The resulting transform is exactly `timeFourier`, including
its measure and phase conventions.
-/

public section

open WithLp
open scoped FourierTransform SchwartzMap

namespace WaveTurbulence.Fourier

/-- The coordinate Fourier transform, bundled as a Schwartz function. -/
@[expose] noncomputable def coordinateFourierSchwartz {d : ℕ}
    (f : 𝓢((Fin d → ℝ), ℂ)) : 𝓢((Fin d → ℝ), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)) f))

@[simp] theorem coordinateFourierSchwartz_apply {d : ℕ}
    (f : 𝓢((Fin d → ℝ), ℂ)) (ξ : Fin d → ℝ) :
    coordinateFourierSchwartz f ξ = timeFourier f ξ := by
  rw [timeFourier_eq_euclidean]
  rfl

/-- Schwartz functions have summable samples on the integer lattice. -/
theorem schwartz_lattice_summable {d : ℕ} (f : 𝓢((Fin d → ℝ), ℂ)) :
    Summable fun n : Fin d → ℤ => f (fun i => (n i : ℝ)) := by
  have h := ContinuousMap.summable_of_locally_summable_norm
    (schwartz_translates_locally_summable f)
  have hh := (ContinuousMap.hasSum_apply h.hasSum (0 : Fin d → ℝ)).summable
  change Summable (fun n : Fin d → ℤ => f (0 + fun i => (n i : ℝ))) at hh
  simpa only [zero_add] using hh

/-- The Fourier samples required on the dual side of Poisson are summable. -/
theorem coordinateFourier_lattice_summable {d : ℕ} (f : 𝓢((Fin d → ℝ), ℂ)) :
    Summable fun n : Fin d → ℤ => timeFourier f (fun i => (n i : ℝ)) := by
  simpa only [coordinateFourierSchwartz_apply] using
    schwartz_lattice_summable (coordinateFourierSchwartz f)

end WaveTurbulence.Fourier
