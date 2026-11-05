/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineFourIncidences
public import WaveTurbulence.Foundations.Molecule.VineNeighborMultiset
import Mathlib.Tactic

/-! # Complete actual four-dart rows determine filtered neighbor multisets -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Filtering the four actual darts to a selected atomic group simply
filters their recorded neighbors. Repetitions retain their multiplicities. -/
theorem fourIncidences_neighbors (M : Molecule V D) (hM : M.IsMolecule)
    {v : V} {neighbors : Fin 4 → V} (R : FourIncidences M v neighbors)
    (A : Finset V) (hv : v ∈ A) (f : V → ℕ) :
    mappedGroupNeighbors M A f v=
      ((univ : Finset (Fin 4)).filter (fun i => neighbors i ∈ A)).val.map
        (fun i => f (neighbors i)) := by
  unfold mappedGroupNeighbors
  rw [← fourIncidences_image M hM R,filter_image]
  have hpred (i : Fin 4) : M.InGroup A (R.dart i) ↔ neighbors i ∈ A := by
    simp only [Molecule.InGroup,R.atom_eq,R.neighbor_eq,hv,true_and]
  simp only [hpred]
  rw [Finset.image_val_of_injOn (fun _ _ _ _ he => R.injective he),Multiset.map_map]
  congr 1
  funext i
  exact congrArg f (R.neighbor_eq i)

end WaveTurbulence.Vine
