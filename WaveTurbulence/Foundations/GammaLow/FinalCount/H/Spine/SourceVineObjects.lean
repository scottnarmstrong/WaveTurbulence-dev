/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceVineObjects`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Source vine-like object definitions copied from the completed VINES interface.
Only the namespace and the definitionally identical Molecule.eraseBond adapter change. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine.SourceVine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
-- (`IsSomeVine`: defined by L6 as `Src.IsSomeVine`)
-- (`Chain`: defined by L6 as `Src.Chain`)
-- (`IsVC`: defined by L6 as `Src.IsVC`)
-- (`IsHV`: defined by L6 as `Src.IsHV`)
-- (`IsHVC`: defined by L6 as `Src.IsHVC`)
-- (`IsDV`: defined by L6 as `Src.IsDV`)
-- (`IsVineLike`: defined by L6 as `Src.IsVineLike`)
-- (`HyperLikeRealization`: defined by L6 as `Src.HyperLikeRealization`)
end WaveTurbulence.GammaLow.FinalCount.H
