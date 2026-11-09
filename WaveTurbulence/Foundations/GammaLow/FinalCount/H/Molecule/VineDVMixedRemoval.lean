/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineDVMixedRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVOrdinaryRemoval
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineDVMixedRemoval`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Simultaneous ordinary and adjoint removals preserve a DV -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, simultaneous mixed-removal clause for a DV. The
geometry needs no SG restriction on the selected ordinary vines or actual
hyper-block adjoints, so it includes the source SG family directly. -/
theorem mixed_vines_removal_in_DV_connected (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (hU : Src.IsDV Src.γL M U a b)
    (ps : List (RemovalPiece V D)) (qs : List (AdjointPiece M))
    (hvine : ∀ P ∈ ps,Src.IsSomeVine Src.γL M P.atoms P.left P.right)
    (hsub : ∀ P ∈ ps,P.atoms ⊆ U)
    (hD : ∀ P ∈ ps,P.darts=univ.filter (M.InGroup P.atoms))
    (hdis : ∀ P ∈ ps,∀ Q ∈ ps,P ≠ Q → Disjoint P.atoms Q.atoms)
    (hQsub : ∀ Q ∈ qs,Q.atoms ⊆ U)
    (hQdis : ∀ P ∈ qs,∀ Q ∈ qs,P ≠ Q → Disjoint P.atoms Q.atoms)
    (hcross : ∀ P ∈ ps,∀ Q ∈ qs,Disjoint P.atoms Q.atoms) :
    ∀ u ∈ remainingAtoms U (ps++qs.map AdjointPiece.toRemoval),
      ∀ v ∈ remainingAtoms U (ps++qs.map AdjointPiece.toRemoval),
      (removeBlocks M U (ps++qs.map AdjointPiece.toRemoval)).SameComponent u v := by
  apply mixed_removal_connected_of_ordinary M hM U ps qs hQsub hQdis hcross
  · intro P hP d hd
    rw [hD P hP] at hd
    exact (mem_filter.mp hd).2
  · exact ordinary_vines_removal_in_DV_connected M hM hU ps hvine hsub hD hdis

end WaveTurbulence.GammaLow.FinalCount.H
