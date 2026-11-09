/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Glue.Fixedpoint
public import WaveTurbulence.Foundations.XChain.V2Chain.PropansatzS
public import Mathlib
public import WaveTurbulence.Frozen.Defs.AnsatzAt
public import WaveTurbulence.Frozen.Defs.IsGaussianData
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTPrefix

/-! # L0 GLUE: `propansatz` (v1) from FL-low and LG-low

Provider skeleton (conditional helper, distinct name). `V2Chain.propansatzS_of_gates` at `S = univ` (as main's
`V2Chain.propansatz_v2_of_gates`) from `layergarden` (`layergarden_of_low`), `fixedpoint` (`fixedpoint_of_low`) and the
sealed `wkeTaylor`. Its conclusion is the type of the frozen DRAFT_SORRY anchor `WaveTurbulence.propansatz`
(`Frozen/Theorems/Propansatz.lean`), pasted verbatim. -/

public section

universe u

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.GammaLow.Glue

/-- **`propansatz` (v1, `0 < γ < 1`) from FL-low and LG-low.** -/
theorem propansatz_of_low (hFL : WaveTurbulence.GammaLow.Flower.LayergardenFlowerLowGate) (hLG : WaveTurbulence.GammaLow.LGLow.LayergardenLowGate) : WTPrefix fun P =>
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
    ∃ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
      (E : ℕ → (Fin P.d → ℤ) → ℝ)
      (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
      ∀ p ≤ P.D, AnsatzAt P μ g a Fev R E Et p := by
  have hL : WTPrefix Induct.LayergardenBody := layergarden_of_low hLG
  have hF : WTPrefix Induct.FixedpointBody.{u} := fixedpoint_of_low hFL hLG
  have hW : WTPrefix Induct.WkeTaylorBody := WaveTurbulence.wkeTaylor
  exact toFull (V2Chain.propansatzS_of_gates (S := Set.univ) (V2Chain.WTPrefixS.ofFull hL)
    (V2Chain.WTPrefixS.ofFull hF) (V2Chain.WTPrefixS.ofFull hW))

end WaveTurbulence.GammaLow.Glue
