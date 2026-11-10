/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentConstantMonotonicity
public import WaveTurbulence.Foundations.Spine.IncoherentSmallParameters
public import WaveTurbulence.Foundations.Spine.IncoherentSpatialAbsorption
public import WaveTurbulence.Foundations.Spine.IncoherentOrderZero
public import WaveTurbulence.Foundations.Spine.StageInputBounds
public import WaveTurbulence.Foundations.Spine.CoherentStageThresholds
/-! Exact source-prefix assembly of the incoherent regular-couple spatial contribution. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Filter

abbrev IncoherentEvenComparisonAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ t ∈ Icc (p : ℝ) (p + 1),
    SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1))
      (incoherentCoupleSum P (inputsF P R) (p + 1) (2 * n) t) ≤
      ENNReal.ofReal (P.δ ^ ((n : ℝ) / 2) *
        P.L ^ (-((3 * P.theta (p + 1) + 2 * P.theta p) / 5)))

end WaveTurbulence.LGSpine
