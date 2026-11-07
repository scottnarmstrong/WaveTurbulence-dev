/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CoupleRemainder
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.IsBalancedSig
public import WaveTurbulence.Frozen.Defs.JbrProd
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RemainderBound
public import WaveTurbulence.Frozen.Defs.SNorm
public import WaveTurbulence.Frozen.Defs.TruncSum
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTParamsR
public import WaveTurbulence.Frozen.Defs.WTParamsTheta
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Foundations.VineEst.V5Proof

/-!
# Provider for `WaveTurbulence.layergarden_v2` (the γ ∈ (1/2, 1) successor, ruling D10)

The proof of the frozen anchor `WaveTurbulence.layergarden_v2` (T Prop `layergarden`, L761–L779; T L776; WAVE-B v2 §4.2; T L762) is assembled here under the export
`WaveTurbulence.Provider.layergarden_v2`. The proof is batch 4b-3's `WaveTurbulence.VineEst.layergarden_v2_proof`
(`Foundations/VineEst/V5Proof`): batch 4b-2's `Spine.layergarden_v2_of_V5` applied to the kind-generic vine
estimate `VineEst.vineEstCanonLayerHalfMK` (TARGET Prop `vineest`). This module must not import the frozen anchor.
-/

public section

public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence.Provider

/-- The frozen statement of `WaveTurbulence.layergarden_v2`, verbatim, proved by batch 4b-3. -/
theorem layergarden_v2 : WTPrefix fun P => 1 / 2 < P.γ →
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioc (p : ℝ) (p + 1), ∀ N ≤ P.N (p + 1) ^ 4,
      (∀ m : ℕ, 2 ≤ m → m ≤ 10 * P.R (p + 1) → ∀ ζ : Fin (2 * m) → ℤˣ, IsBalancedSig ζ →
        ∀ n : Fin (2 * m) → (Fin P.d → ℤ),
          ‖truncSum P (inputsF P R) (p + 1) N t ζ n‖ ≤
            jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) *
              P.δ ^ (2 * P.ν * N)) ∧
      (∀ n : Fin 2 → (Fin P.d → ℤ), n 0 ≠ n 1 →
        truncSum P (inputsF P R) (p + 1) N t ![1, -1] n = 0) ∧
      SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (coupleRemainder P R p N t) ≤
        ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) * P.δ ^ (2 * P.ν * N)) :=
  WaveTurbulence.VineEst.layergarden_v2_proof

end WaveTurbulence.Provider
