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
import WaveTurbulence.Frozen.Theorems.LayergardenV2
import WaveTurbulence.Frozen.Theorems.FixedpointV2
import WaveTurbulence.Frozen.Theorems.WkeTaylor
import WaveTurbulence.Foundations.XChain.V2Chain.PropansatzV2

/-!
# Provider for `WaveTurbulence.propansatz_v2` (the γ ∈ (1/2, 1) successor, ruling D10)

The proof of the frozen anchor `WaveTurbulence.propansatz_v2` (T Prop `propansatz`, L689–L707; WAVE-B v2 §4.1; T L819) is assembled here under the export
`WaveTurbulence.Provider.propansatz_v2`.
The proof is `V2Chain.propansatz_v2_of_gates` (`Foundations/XChain/V2Chain/PropansatzV2`, the induction
over the layers p ≤ 𝔇 of TARGET Prop `propansatz`) applied to the sealed anchors `layergarden_v2`,
`fixedpoint_v2` and `wkeTaylor`. This module must not import its own frozen anchor.
The proof modules are imported privately (`import`), so that the frozen anchor elaborates its statement
in its freeze environment.
-/

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
universe u

namespace WaveTurbulence.Provider

/-- The frozen statement of `WaveTurbulence.propansatz_v2`, verbatim,
proved by the assembly in the module docstring. -/
theorem propansatz_v2 : WTPrefix fun P => 1 / 2 < P.γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
    ∃ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
      (E : ℕ → (Fin P.d → ℤ) → ℝ)
      (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
      ∀ p ≤ P.D, AnsatzAt P μ g a Fev R E Et p :=
  WaveTurbulence.V2Chain.propansatz_v2_of_gates WaveTurbulence.layergarden_v2
    WaveTurbulence.fixedpoint_v2 WaveTurbulence.wkeTaylor

end WaveTurbulence.Provider
