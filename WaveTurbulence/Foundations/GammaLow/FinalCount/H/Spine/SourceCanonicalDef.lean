/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCanonicalDef
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceCanonicalDef`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 R6(a): one canonical designation per atom set of the second collection.

READING (source ambiguity, not an erratum): in TARGET an HV/HVC vine-like object is an atomic
group, so it has one designation. The Lean `Object` keeps the deleted bond, so two different
deleted bonds of one atom set are two objects. The selection of the collection is assembly
(RULINGS R3/R6(a)); we select, among the members of the collection with one hyper atom set, the one
whose deleted bond (up to mates) is least for a fixed injective rank `rk` on darts. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

-- (`SourceVine.Object.hyperRank`: defined by L6 as `Src.SourceVine.Object.hyperRank`)
-- (`canonicalSub`: defined by L6 as `Src.canonicalSub`)
theorem canonicalSub_subset {M : Molecule V D} (rk : D → ℕ) (K : Set (Src.Object Src.γL M)) :
    Src.canonicalSub rk K ⊆ K := fun _ h => h.1

end WaveTurbulence.GammaLow.FinalCount.H
