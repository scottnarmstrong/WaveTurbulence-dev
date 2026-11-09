/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceCountingObjects`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Explicit object selection in TARGET L2101–L2104: maximal SG objects inside DV/LG/ZG
containers, with one constituent omitted when both type-V constituents of a DV are SG. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.SourceVine
open Set Finset
variable {w d : ℕ}

-- (`Object.ofVine`: defined by L6 as `Src.Object.ofVine`)
-- (`DoubleVine`: defined by L6 as `Src.DoubleVine`)
-- (`eligibleSecondObject`: defined by L6 as `Src.eligibleSecondObject`)
-- (`IsSourceSecondCollection`: defined by L6 as `Src.IsSourceSecondCollection`)
-- (`Object.IsInterior`: defined by L6 as `Src.Object.IsInterior`)
end WaveTurbulence.GammaLow.FinalCount.H
