/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineTwoIncidenceExtraction
public import WaveTurbulence.Foundations.Molecule.VineRailNeighbors
import Mathlib.Tactic

/-! # Extract doubled incidences from literal edge multiplicities -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- A repeated mapped neighbor label yields two actual distinct darts,
using only the relevant fiber rather than a complete neighbor row. -/
theorem twoIncidences_of_mapped_count (M : Molecule V D) (S : Finset V) (f : V → ℕ)
    (hf : Set.InjOn f S) (x y : V) (hy : y ∈ S)
    (hc : 2 ≤ (mappedGroupNeighbors M S f x).count (f y)) : Nonempty (TwoIncidences M x y) := by
  classical
  let T := ((M.dartsAt x).filter (M.InGroup S)).filter (fun d => f y=f (M.atom (M.mate d)))
  have he : (mappedGroupNeighbors M S f x).count (f y)=T.card := by
    simp only [mappedGroupNeighbors,Multiset.count_map,← filter_val,Finset.card_val,T]
  have hcard : Fintype.card (Fin 2) ≤ T.card := by rw [Fintype.card_fin,← he]; exact hc
  obtain ⟨g,hg⟩ := Function.Embedding.exists_of_card_le_finset hcard
  have hmem (i : Fin 2) : g i ∈ T := hg ⟨i,rfl⟩
  refine ⟨⟨g,g.injective,?_,?_⟩⟩
  · intro i
    exact (Mole.mem_dartsAt M x _).mp (mem_filter.mp (mem_filter.mp (hmem i)).1).1
  · intro i
    have hm := mem_filter.mp (hmem i)
    exact hf (mem_filter.mp hm.1).2.2 hy hm.2.symm

/-- Every literal copy of (x,y) contributes an incidence from x to y.
This lower bound is valid even when other parallel or reversed edges occur. -/
theorem edge_count_le_neighbor_count (es : List (ℕ×ℕ)) (x y : ℕ) :
    es.count (x,y) ≤ (edgeListNeighbors es x).count y := by
  induction es with
  | nil => simp [edgeListNeighbors]
  | cons e es ih =>
    rw [edgeListNeighbors_cons,Multiset.count_add,Multiset.count_add]
    by_cases he : e=(x,y)
    · subst e
      rw [List.count_cons_self]
      simp only [ite_true,Multiset.count_singleton_self]
      omega
    · rw [List.count_cons_of_ne he]
      omega

/-- The pinned realization extracts a doubled actual bond from any two
literal parallel copies, with no full incidence-row assumption. -/
theorem VineRealization.twoIncidences_of_edge_count {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (hc : 2 ≤ (X.expand R.k).bonds.count (R.f x,R.f y)) : Nonempty (TwoIncidences M x y) := by
  apply twoIncidences_of_mapped_count M S R.f R.injOn x y hy
  rw [R.neighbors hx]
  exact hc.trans (edge_count_le_neighbor_count _ _ _)

end WaveTurbulence.Vine
