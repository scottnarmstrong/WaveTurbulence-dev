/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCanonicalDef
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceCountingData`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Literal fixed choices in the spliced counting problem, TARGET L2097–L2116. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.SourceVine
open Set Finset
variable {w d : ℕ}

-- (`CountingChoices`: defined by L6 as `Src.CountingChoices`)
-- (`CountingChoices.CriticalSG`: defined by L6 as `Src.CountingChoices.CriticalSG`)
-- (`CountingChoices.numCriticalSG`: defined by L6 as `Src.CountingChoices.numCriticalSG`)
-- (`SubproChoices.forbidden`: defined by L6 as `Src.SubproChoices.forbidden`)
-- (`CountingChoices.SecondCollectionOK`: defined by L6 as `Src.CountingChoices.SecondCollectionOK`)
-- (`CountingChoices.LadderGaps`: defined by L6 as `Src.CountingChoices.LadderGaps`)
-- (`CountingChoices.Admissible`: defined by L6 as `Src.CountingChoices.Admissible`)
-- (`CountingGeometry`: defined by L6 as `Src.CountingGeometry`)
-- (`CountingGeometry.hinges_card_le`: defined by L6 as `Src.CountingGeometry.hinges_card_le`)
end WaveTurbulence.GammaLow.FinalCount.H
