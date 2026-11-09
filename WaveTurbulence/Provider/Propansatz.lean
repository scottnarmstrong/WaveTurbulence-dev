/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.AnsatzAt
public import WaveTurbulence.Frozen.Defs.IsGaussianData
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTPrefix
import WaveTurbulence.Foundations.GammaLow.Glue.Propansatz
import WaveTurbulence.Foundations.GammaLow.Close.Final
import WaveTurbulence.Foundations.GammaLow.Close.Halves

/-!
# Provider for `WaveTurbulence.propansatz`

The proof of the frozen anchor `WaveTurbulence.propansatz` (T Prop `propansatz`, L689–L707; WAVE-B v2 §4.1; T L819) is assembled here under the export
`WaveTurbulence.Provider.propansatz`.
The proof is the L07 glue `GammaLow.Glue.propansatz_of_low` (`Foundations/GammaLow/Glue/Propansatz`:
`V2Chain.propansatzS_of_gates` at `S = univ`, the induction over the layers p ≤ 𝔇) applied to the
closed theorems `WaveTurbulence.GammaLow.Close.flower_low_closed` (`WaveTurbulence.Foundations.GammaLow.Close.Final`) and `WaveTurbulence.GammaLow.Close.layergarden_low_closed` (`WaveTurbulence.Foundations.GammaLow.Close.Halves`).
The proof modules are imported privately (`import`), so that the frozen anchor
elaborates its statement in its freeze environment. This module must not import its own frozen anchor.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence.Provider

/-- The frozen statement of `WaveTurbulence.propansatz`, verbatim,
proved by the assembly in the module docstring. -/
theorem propansatz : WTPrefix fun P =>
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
    ∃ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
      (E : ℕ → (Fin P.d → ℤ) → ℝ)
      (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
      ∀ p ≤ P.D, AnsatzAt P μ g a Fev R E Et p :=
  WaveTurbulence.GammaLow.Glue.propansatz_of_low WaveTurbulence.GammaLow.Close.flower_low_closed WaveTurbulence.GammaLow.Close.layergarden_low_closed

end WaveTurbulence.Provider
