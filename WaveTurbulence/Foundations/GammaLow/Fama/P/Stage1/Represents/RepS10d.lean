/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a-G: main `WaveTurbulence.Foundations.Stage1.Represents.RepS10d` over 𝒱_γ (sha256 in COPIED-SHA256SUMS-G).
module
public import WaveTurbulence.Foundations.GammaLow.Fama.VineCase
public import WaveTurbulence.Foundations.Stage1.Represents.RepS10d
/-! # S2 REPRESENTS, session 10, over `𝒱_γ`: superseded

Main's `RepS10d` proves `LargeConstantMonotone NoVineRepresentsAtN` and `LargeConstantMonotone VineCaseRepresents`.
Over `𝒱_γ` these predicates need `[Fact (P.γ ≤ 1 / 2)]`, so the monotone statements are L5a's `γ ≤ 1/2` forms
`noVineRepresentsLow_mono`, `vineCaseRepresentsLow_mono` (L5a's `Fama/VineCase.lean`), proved by main's argument in
`Fama/VineCaseProof.lean`. The family-free `leafFamily_size_nonneg` is main's (imported). -/
