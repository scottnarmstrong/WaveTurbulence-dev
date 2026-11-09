/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceSubproObjects`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Literal structural and decorated conclusions of TARGET subpro, L2040–L2051.
These predicates describe the output of the stage-one reduction; they do not assert the
reduction theorem or the disputed counting bound. Provider: S4 (SUBPRO). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.SourceVine
open Finset
variable {w d : ℕ}

-- (`SubproChoices`: defined by L6 as `Src.SubproChoices`)
-- (`SubproChoices.TripleDesignated`: defined by L6 as `Src.SubproChoices.TripleDesignated`)
-- (`SubproChoices.HingeNoLoop`: defined by L6 as `Src.SubproChoices.HingeNoLoop`)
-- (`SubproChoices.Structural`: defined by L6 as `Src.SubproChoices.Structural`)
-- (`SubproChoices.Outside`: defined by L6 as `Src.SubproChoices.Outside`)
-- (`SubproChoices.OutsideAtoms`: defined by L6 as `Src.SubproChoices.OutsideAtoms`)
-- (`SubproSupport`: defined by L6 as `Src.SubproSupport`)
end WaveTurbulence.GammaLow.FinalCount.H
