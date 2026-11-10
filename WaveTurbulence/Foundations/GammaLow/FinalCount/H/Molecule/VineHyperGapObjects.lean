/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineHyperGapObjects`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Hyper-vine-like gaps retain their designated adjoint bond

Owner reading 2026-11-04: a hyper-block object retains its actual designated
joint bond. Different valid deletions on one atom group are different objects.
The gap uses this same designation throughout, as TARGET defdiff requires.
No pinned definition is altered; the existential shape predicates remain useful.
-/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

-- (`HyperLikeRealization`: defined by L6 as `Src.HyperLikeRealization`)
/-- Erasing the designated data recovers exactly the existential HV/HVC shape. -/
theorem hyperLike_iff_realization {M : Molecule V D} {S : Finset V} {a b : V} :
    (Src.IsHV Src.γL M S a b ∨ Src.IsHVC Src.γL M S a b) ↔ Nonempty (Src.HyperLikeRealization Src.γL M S a b) := by
  rw [hyperLike_iff_adjoint_VC]
  constructor
  · rintro ⟨e,he,hVC⟩
    exact ⟨⟨e,he,hVC⟩⟩
  · rintro ⟨R⟩
    exact ⟨R.added,R.ends_eq,R.adjoint⟩

namespace Src.HyperLikeRealization
open Src.HyperLikeRealization
variable {M : Molecule V D} {S : Finset V} {a b : V} (R : Src.HyperLikeRealization Src.γL M S a b)

-- (`HyperLikeRealization.IsGap`: defined by L6 as `Src.HyperLikeRealization.IsGap`)
-- (`HyperLikeRealization.IsContained`: defined by L6 as `Src.HyperLikeRealization.IsContained`)

end Src.HyperLikeRealization
end WaveTurbulence.GammaLow.FinalCount.H
