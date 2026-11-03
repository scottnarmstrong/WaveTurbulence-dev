/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.LatticeConvergence
import Mathlib.Tactic

/-!
# Continuous Schwartz periodization

Integer translates of a Schwartz function define a continuous periodic
function in every dimension, with the sum understood in the compact-open
topology. This is the periodization used in Poisson summation.
-/

public section

open scoped SchwartzMap

namespace WaveTurbulence.Fourier

/-- Periodization over the standard integer lattice, as a continuous map. -/
@[expose] noncomputable def schwartzPeriodization {d : ℕ} (f : 𝓢((Fin d → ℝ), ℂ)) :
    C((Fin d → ℝ), ℂ) :=
  ∑' n : Fin d → ℤ, f.toContinuousMap.comp (ContinuousMap.addRight (fun i => (n i : ℝ)))

/-- The compact-open sum agrees with the pointwise lattice sum. -/
theorem schwartzPeriodization_apply {d : ℕ} (f : 𝓢((Fin d → ℝ), ℂ)) (x : Fin d → ℝ) :
    schwartzPeriodization f x = ∑' n : Fin d → ℤ, f (x + fun i => (n i : ℝ)) := by
  exact (ContinuousMap.tsum_apply
    (ContinuousMap.summable_of_locally_summable_norm (schwartz_translates_locally_summable f)) x).symm

/-- Integer periodization is periodic in each coordinate. -/
theorem schwartzPeriodization_periodic {d : ℕ} (f : 𝓢((Fin d → ℝ), ℂ)) :
    WaveTurbulence.IsTorusPeriodic 1 (schwartzPeriodization f) := by
  classical
  intro j x
  simp only [schwartzPeriodization_apply]
  have he := (Equiv.addRight (Pi.single j (1 : ℤ))).tsum_eq
    (fun n : Fin d → ℤ => f (x + fun i => (n i : ℝ)))
  rw [← he]
  apply tsum_congr
  intro n
  congr 1
  ext i
  by_cases hi : i = j
  · subst i
    simp [Pi.single_apply, add_comm, add_left_comm]
  · simp [Pi.single_apply, hi]

end WaveTurbulence.Fourier
