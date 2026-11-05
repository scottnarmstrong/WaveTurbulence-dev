/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineFourNeighborRows
import Mathlib.Tactic

/-! # The four-term formula for actual selected neighbor rows -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Expand a complete recorded row into four membership-filtered singleton
contributions, preserving repeated neighbors and repeated labels. -/
theorem fourIncidences_neighbors_formula (M : Molecule V D) (hM : M.IsMolecule)
    {v : V} {neighbors : Fin 4 → V} (R : FourIncidences M v neighbors)
    (A : Finset V) (hv : v ∈ A) (f : V → ℕ) :
    mappedGroupNeighbors M A f v=
      (if neighbors 0 ∈ A then {f (neighbors 0)} else 0)+
      (if neighbors 1 ∈ A then {f (neighbors 1)} else 0)+
      (if neighbors 2 ∈ A then {f (neighbors 2)} else 0)+
      (if neighbors 3 ∈ A then {f (neighbors 3)} else 0) := by
  rw [fourIncidences_neighbors M hM R A hv f,filter_val]
  have hu : (univ : Finset (Fin 4)).val=([0,1,2,3] : List (Fin 4)) := by decide
  rw [hu]
  by_cases h0 : neighbors 0 ∈ A <;> by_cases h1 : neighbors 1 ∈ A <;>
    by_cases h2 : neighbors 2 ∈ A <;> by_cases h3 : neighbors 3 ∈ A <;>
    simp [h0,h1,h2,h3]
  all_goals rfl

/-- The four-term formula specialized to a recorded literal neighbor tuple. -/
theorem fourIncidences_neighbors_tuple (M : Molecule V D) (hM : M.IsMolecule)
    {v a b c d : V} (R : FourIncidences M v ![a,b,c,d])
    (A : Finset V) (hv : v ∈ A) (f : V → ℕ) :
    mappedGroupNeighbors M A f v=
      (if a ∈ A then {f a} else 0)+(if b ∈ A then {f b} else 0)+
      (if c ∈ A then {f c} else 0)+(if d ∈ A then {f d} else 0) :=
  fourIncidences_neighbors_formula M hM R A hv f

end WaveTurbulence.Vine
