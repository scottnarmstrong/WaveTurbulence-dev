/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceVineData`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Explicit source objects used by subpro and the finalcount1 admissibility requirements. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.SourceVine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

-- (`Object`: defined by L6 as `Src.Object`)
namespace Src.Object
open Src.Object
variable {M : Molecule V D}

-- (`Object.HasGapKind`: defined by L6 as `Src.Object.HasGapKind`)
-- (`Object.IsContained`: defined by L6 as `Src.Object.IsContained`)
-- (`Object.ContainsDart`: defined by L6 as `Src.Object.ContainsDart`)
end Src.Object

-- (`AllowedCollectionObject`: defined by L6 as `Src.AllowedCollectionObject`)
end WaveTurbulence.GammaLow.FinalCount.H
