/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineFiniteMatching
public import WaveTurbulence.Foundations.Molecule.VineNeighborMultiset
public import WaveTurbulence.Foundations.Molecule.VineDoublePairClosure
import Mathlib.Tactic

/-! # Extract doubled incidence witnesses from exact neighbor multisets -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- An exact two-neighbor multiset gives two distinct actual darts.
Repeated neighbors are matched by fiber cardinality; no orientation choices
or incidence witnesses are assumed. -/
theorem exists_twoIncidences_of_neighbors (M : Molecule V D) (S : Finset V) (f : V → ℕ)
    (hf : Set.InjOn f S) (v : V) (neighbors : Fin 2 → V) (hn : ∀ i,neighbors i ∈ S)
    (hequal : neighbors 1=neighbors 0)
    (hlabels : mappedGroupNeighbors M S f v=
      (univ : Finset (Fin 2)).val.map (fun i => f (neighbors i))) :
    Nonempty (TwoIncidences M v (neighbors 0)) := by
  classical
  let T := (M.dartsAt v).filter (M.InGroup S)
  let label : T → ℕ := fun x => f (M.atom (M.mate x.1))
  have hs : (univ : Finset T).val.map label=mappedGroupNeighbors M S f v := by
    simpa only [T,label,mappedGroupNeighbors] using
      univ_subtype_map T (fun x => f (M.atom (M.mate x)))
  have hm : (univ : Finset (Fin 2)).val.map (fun i => f (neighbors i))=
      (univ : Finset T).val.map label := hlabels.symm.trans hs.symm
  obtain ⟨e,he⟩ := exists_label_matching (fun i : Fin 2 => f (neighbors i)) label hm
  refine ⟨⟨fun i => (e i).1,?_,?_,?_⟩⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    exact (Mole.mem_dartsAt M v _).mp (mem_filter.mp (e i).2).1
  · intro i
    have hmem := (mem_filter.mp (e i).2).2
    have hh := hf hmem.2 (hn i) (he i)
    have hn0 : neighbors i=neighbors 0 := by fin_cases i; rfl; exact hequal
    exact hh.trans hn0

end WaveTurbulence.Vine
