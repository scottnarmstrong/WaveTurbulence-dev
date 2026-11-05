/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineDVOrdinaryRemoval
public import WaveTurbulence.Foundations.Molecule.VineMixedAdjointRetraction
import Mathlib.Tactic

/-! # Simultaneous ordinary and adjoint removals preserve a DV -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET subsetvc, simultaneous mixed-removal clause for a DV. The
geometry needs no SG restriction on the selected ordinary vines or actual
hyper-block adjoints, so it includes the source SG family directly. -/
theorem mixed_vines_removal_in_DV_connected (M : Molecule V D) (hM : M.IsMolecule)
    {U : Finset V} {a b : V} (hU : IsDV M U a b)
    (ps : List (RemovalPiece V D)) (qs : List (AdjointPiece M))
    (hvine : ∀ P ∈ ps,IsSomeVine M P.atoms P.left P.right)
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

end WaveTurbulence.Vine
