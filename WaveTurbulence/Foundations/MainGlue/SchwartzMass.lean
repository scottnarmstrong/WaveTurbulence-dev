/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.MainGlue.MassEvent
public import WaveTurbulence.Foundations.MainGlue.LatticeSum

/-!
# G6–G7: the mass-event estimate for the frozen initial datum

SEAL-PLAN §B.4. The event is arbitrary and no independence assumption is
needed. The constant in the scaled bound depends only on the Schwartz
profile and dimension, before the probability data and event are supplied.
-/

public section

namespace WaveTurbulence.MainGlue
open MeasureTheory ProbabilityTheory
open scoped SchwartzMap

/-- G6 in the exact sampled-envelope form proposed in the seal plan. -/
theorem integral_initial_mass_restrict_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {L : ℝ} (hL : 0 < L)
    (φ : 𝓢(Mom d, ℝ)) (hφ : ∀ k, 0 ≤ φ k) (g : (Fin d → ℤ) → Ω → ℂ)
    (hg : ∀ n, HasLaw (g n) stdComplexGaussian P) (A : Set Ω) :
    (∫ ω in A, ∑' n, φ (latticePoint L n) * ‖g n ω‖ ^ 2 ∂P) ≤
      Real.sqrt 2 * Real.sqrt (P.real A) * ∑' n, φ (latticePoint L n) :=
  integral_gaussian_mass_restrict_le g hg _ (fun _ => hφ _)
    (summable_schwartz_lattice φ hL) A

end WaveTurbulence.MainGlue
