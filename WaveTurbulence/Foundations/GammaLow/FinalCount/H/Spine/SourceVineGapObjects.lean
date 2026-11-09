/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceVineGapObjects`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Literal designated vine gaps and containment for the subpro/finalcount source inputs.
The designated hyper-adjoint convention is copied from the completed VINES interface. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.SourceVine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace Src.HyperLikeRealization
open Src.HyperLikeRealization
variable {M : Molecule V D} {S : Finset V} {a b : V}
-- (`HyperLikeRealization.IsGap`: defined by L6 as `Src.HyperLikeRealization.IsGap`)
-- (`HyperLikeRealization.IsContained`: defined by L6 as `Src.HyperLikeRealization.IsContained`)
end Src.HyperLikeRealization
-- (`VineLikeObject`: defined by L6 as `Src.VineLikeObject`)
namespace Src.VineLikeObject
open Src.VineLikeObject
variable {M : Molecule V D} {S A : Finset V} {a b x y : V}

-- (`VineLikeObject.IsGap`: defined by L6 as `Src.VineLikeObject.IsGap`)
-- (`VineLikeObject.IsContained`: defined by L6 as `Src.VineLikeObject.IsContained`)
end Src.VineLikeObject
end WaveTurbulence.GammaLow.FinalCount.H
