/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentAllOrdersSpatialComparison
public import WaveTurbulence.Foundations.Spine.CoherentSourcePrefix
public import WaveTurbulence.Foundations.Spine.CoherentSmallParameters
public import WaveTurbulence.Foundations.Spine.CoherentStageThresholds
public import WaveTurbulence.Foundations.Spine.CoherentProfileInputBounds
/-! Parameter-prefix assembly of the coherent even-order leg of TARGET L2253–2255. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Filter

abbrev CoherentEvenComparisonAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ t ∈ Icc (p : ℝ) (p + 1),
    SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
      (fun k => coherentCoupleSum P (inputsF P R) (p + 1) (2 * n) t k -
        (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)) ≤
      ENNReal.ofReal (P.δ ^ ((n : ℝ) / 2) *
        P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))

end WaveTurbulence.LGSpine
