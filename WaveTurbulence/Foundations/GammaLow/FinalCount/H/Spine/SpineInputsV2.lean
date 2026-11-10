/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpineInputsV2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.MolecularSpineAt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCanonicalDesignation
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SpineInputsV2`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 The D9/D10 successor `layergarden_v2` (restricted to `1/2 < γ`) from the spine inputs, with the
final-count gate restricted to `1/2 < γ` as the only change of hypothesis (`FinalCountGateHalf`).

**Low-range restatement (L6-HMS2, GAMMA row; PLAN-L6 §3f rule 4).** In the port the range `1/2 < γ` becomes
`γ ≤ 1/2`: `FinalCountGateHalf` is `WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAt P` (the ported `FinalCountAt` is the body
of L6's `FinalCountLAt`, so this is the hypothesis of `finalCountGateLow_of_L`), and `finalCountHalf_largeConstantMonotone`
and `nonregular_prefix_half` are restated with `P.γ ≤ 1 / 2` (same proofs). Main's `layergarden_v2_of_spine` is not
ported: its conclusion is main's frozen `LayergardenV2Gate` (range `1/2 < γ`), it has no consumer in the ported run,
and the γ ≤ 1/2 assembly of the layer-garden statements is outside the ported run (wt-orch's LG-low/FL-low). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set MeasureTheory
open scoped ENNReal

/-- Row 6 restricted to the low range `γ ≤ 1/2` (main: `1/2 < γ`). -/
abbrev FinalCountGateHalf : Prop := WTPrefix fun P => P.γ ≤ 1 / 2 → FinalCountAt P

end WaveTurbulence.GammaLow.FinalCount.H
