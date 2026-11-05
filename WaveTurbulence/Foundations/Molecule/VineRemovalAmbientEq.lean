/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRemoval
import Mathlib.Tactic

/-! # Transport removal paths across equal ambient atom groups -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V]

/-- Equal ambient atom groups give the same surviving path relation,
including its dependent surviving-dart carrier. -/
theorem removal_path_change_ambient (M : Molecule V D) (ps : List (RemovalPiece V D))
    {S U : Finset V} (he : S=U) {u v : V} (hp : (removeBlocks M S ps).SameComponent u v) :
    (removeBlocks M U ps).SameComponent u v := by
  subst U
  exact hp

/-- Connectivity after removal is invariant under equality of the
ambient atom group. This avoids rewriting implicit dependent dart types. -/
theorem removal_connected_change_ambient (M : Molecule V D) (ps : List (RemovalPiece V D))
    {S U : Finset V} (he : S=U)
    (hconn : ∀ u ∈ remainingAtoms S ps,∀ v ∈ remainingAtoms S ps,(removeBlocks M S ps).SameComponent u v) :
    ∀ u ∈ remainingAtoms U ps,∀ v ∈ remainingAtoms U ps,(removeBlocks M U ps).SameComponent u v := by
  subst U
  exact hconn

end WaveTurbulence.Vine
