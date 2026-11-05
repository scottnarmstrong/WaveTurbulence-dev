/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapNeighborAux
import Mathlib.Tactic

/-! # Every literal triangle-cap neighbor row, including its terminal selected rung -/

public section
namespace WaveTurbulence.Vine

/-- The complete cap row at each finite cap index. At the final selected
rung the successor contribution is absent; at r=0 the triangle legs have no rail. -/
@[expose] def capNeighborRow (r : ℕ) : CapIndex r → Multiset ℕ
  | .inl i => ![{5}+{5}+{6}+{6},
      {4}+{4}+{6}+(if r=0 then 0 else {9}),
      {4}+{4}+{5}+(if r=0 then 0 else {9+r})] i
  | .inr (.inl i) => {9+r+i.1}+{9+r+i.1}+
      {if i.1=0 then 5 else 9+i.1-1}+(if i.1+1<r then {9+i.1+1} else 0)
  | .inr (.inr i) => {9+i.1}+{9+i.1}+
      {if i.1=0 then 6 else 9+r+i.1-1}+(if i.1+1<r then {9+r+i.1+1} else 0)

/-- The raw cap lists have exactly the prescribed finite neighbor rows.
The proof retains parallel bonds and does not presume a vine realization. -/
theorem capBonds_neighbor_row (r : ℕ) (i : CapIndex r) :
    edgeListNeighbors (capBonds 9 r) (capIndexLabel 9 r i)=capNeighborRow r i := by
  cases i with
  | inl i =>
    fin_cases i
    · change edgeListNeighbors (capBonds 9 r) 4={5}+{5}+{6}+{6}
      rw [capBonds]
      simp only [edgeListNeighbors_append]
      rw [capTriangle_neighbors_center,
        openRail_allocated_neighbors_zero 9 5 r 4 (by decide) (Or.inl (by decide)),
        openRail_allocated_neighbors_zero (9+r) 6 r 4 (by omega) (Or.inl (by omega)),
        allocatedRungs_neighbors_zero_before 9 (9+r) r 4 (by decide) (by omega)]
      simp only [add_zero]
    · change edgeListNeighbors (capBonds 9 r) 5={4}+{4}+{6}+(if r=0 then 0 else {9})
      rw [capBonds]
      simp only [edgeListNeighbors_append]
      rw [capTriangle_neighbors_upper,openRail_start_neighbors 9 5 r (by decide),
        openRail_allocated_neighbors_zero (9+r) 6 r 5 (by omega) (Or.inl (by omega)),
        allocatedRungs_neighbors_zero_before 9 (9+r) r 5 (by decide) (by omega)]
      simp only [add_zero]
    · change edgeListNeighbors (capBonds 9 r) 6={4}+{4}+{5}+(if r=0 then 0 else {9+r})
      rw [capBonds]
      simp only [edgeListNeighbors_append]
      rw [capTriangle_neighbors_lower,
        openRail_allocated_neighbors_zero 9 5 r 6 (by decide) (Or.inl (by decide)),
        openRail_start_neighbors (9+r) 6 r (by omega),
        allocatedRungs_neighbors_zero_before 9 (9+r) r 6 (by decide) (by omega)]
      simp only [add_zero]
  | inr i =>
    cases i with
    | inl i =>
      change edgeListNeighbors (capBonds 9 r) (9+i.1)=_
      rw [capBonds]
      simp only [edgeListNeighbors_append]
      rw [capTriangle_neighbors_fresh _ (by omega),
        openRail_allocated_neighbors 9 5 7 r i.1 (by decide) (by decide) i.2,
        openRail_allocated_neighbors_zero (9+r) 6 r (9+i.1) (by omega) (Or.inl (by omega)),
        allocatedRungs_neighbors_left 9 (9+r) r i.1 le_rfl i.2]
      simp only [capNeighborRow,zero_add,add_zero]
      ac_rfl
    | inr i =>
      change edgeListNeighbors (capBonds 9 r) (9+r+i.1)=_
      rw [capBonds]
      simp only [edgeListNeighbors_append]
      rw [capTriangle_neighbors_fresh _ (by omega),
        openRail_allocated_neighbors_zero 9 5 r (9+r+i.1) (by omega) (Or.inr (by omega)),
        openRail_allocated_neighbors (9+r) 6 8 r i.1 (by omega) (by omega) i.2,
        allocatedRungs_neighbors_right 9 (9+r) r i.1 le_rfl i.2]
      simp only [capNeighborRow,zero_add,add_zero]
      ac_rfl

end WaveTurbulence.Vine
