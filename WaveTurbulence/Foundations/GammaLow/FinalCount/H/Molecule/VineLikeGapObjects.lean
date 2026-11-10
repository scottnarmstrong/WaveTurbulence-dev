/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineLikeGapObjects`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Source vine-like objects retain the data needed to specify their gap

Owner reading 2026-11-04: hyper objects retain their designated adjoint bond;
equal hyper atom groups are nested only for the same bond up to mates.
-/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

-- (`VineLikeObject`: defined by L6 as `Src.VineLikeObject`)
namespace Src.VineLikeObject
open Src.VineLikeObject
variable {M : Molecule V D} {S A : Finset V} {a b x y : V}

-- (`VineLikeObject.IsGap`: defined by L6 as `Src.VineLikeObject.IsGap`)
-- (`VineLikeObject.IsContained`: defined by L6 as `Src.VineLikeObject.IsContained`)

/-- Every designated-object containment includes the actual atom containment. -/
theorem atoms_subset (P : Src.VineLikeObject Src.γL M A x y) (C : Src.VineLikeObject Src.γL M S a b)
    (h : P.IsContained C) : A ⊆ S := by
  cases P <;> cases C
  · exact h
  · exact h
  · exact h
  · exact h.1

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.VineLikeObject.atoms_subset := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.VineLikeObject.atoms_subset
end Src.VineLikeObject
end WaveTurbulence.GammaLow.FinalCount.H
