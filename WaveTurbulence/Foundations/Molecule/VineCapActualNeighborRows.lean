/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapPrefixNeighborTerms
public import WaveTurbulence.Foundations.Molecule.VineCapNeighborRows
public import WaveTurbulence.Foundations.Molecule.VineFourNeighborFormula
import Mathlib.Tactic

/-! # Primitive cap incidence data give the exact literal cap neighbor rows -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace CapPrefixData
variable {M : Molecule V D} {A : Finset V} {n r : ℕ} (C : CapPrefixData M A n r)

/-- Each selected actual cap atom has the exact mapped literal neighbor
row. This is derived from actual four-dart rows and selected-atom membership,
not assumed as a graph-realization premise. -/
theorem mapped_neighbor_row (hM : M.IsMolecule) (i : CapIndex r) :
    mappedGroupNeighbors M A C.label (C.family i)=capNeighborRow r i := by
  cases i with
  | inl i =>
    fin_cases i
    · change mappedGroupNeighbors M A C.label C.center={5}+{5}+{6}+{6}
      rw [fourIncidences_neighbors_tuple M hM C.side.center_row A C.triangle_mem.1 C.label]
      simp only [C.triangle_mem.2.1,
        C.triangle_mem.2.2,ite_true,C.label_triangle.2.1,C.label_triangle.2.2]
    · change mappedGroupNeighbors M A C.label C.upper=
        {4}+{4}+{6}+(if r=0 then 0 else {9})
      rw [fourIncidences_neighbors_tuple M hM C.side.upper_row A C.triangle_mem.2.1 C.label]
      simp only [C.triangle_mem.1,
        C.triangle_mem.2.2,ite_true,C.label_triangle.1,C.label_triangle.2.2]
      rw [C.upper_first_contribution]
    · change mappedGroupNeighbors M A C.label C.lower=
        {4}+{4}+{5}+(if r=0 then 0 else {9+r})
      rw [fourIncidences_neighbors_tuple M hM C.side.lower_row A C.triangle_mem.2.2 C.label]
      simp only [C.triangle_mem.1,
        C.triangle_mem.2.1,ite_true,C.label_triangle.1,C.label_triangle.2.1]
      rw [C.lower_first_contribution]
  | inr i =>
    cases i with
    | inl i =>
      have hj : 1 ≤ i.1+1 := by omega
      have hjn : i.1+1 ≤ n := by have := C.r_le; omega
      have hmem : C.side.ladder.u (i.1+1) ∈ A := C.family_mem (.inr (.inl i))
      have hpart : C.side.ladder.v (i.1+1) ∈ A := C.family_mem (.inr (.inr i))
      change mappedGroupNeighbors M A C.label (C.side.ladder.u (i.1+1))=_
      rw [fourIncidences_neighbors_tuple M hM (C.side.ladder.upper (i.1+1) hj hjn) A hmem C.label]
      simp only [Nat.add_sub_cancel,
        hpart,C.upper_prev_mem i,ite_true,C.label_lower (i.1+1) hj (by omega),
        C.upper_prev_label i]
      rw [show i.1+1+1=i.1+2 by omega,C.upper_next_contribution i]
      rfl
    | inr i =>
      have hj : 1 ≤ i.1+1 := by omega
      have hjn : i.1+1 ≤ n := by have := C.r_le; omega
      have hmem : C.side.ladder.v (i.1+1) ∈ A := C.family_mem (.inr (.inr i))
      have hpart : C.side.ladder.u (i.1+1) ∈ A := C.family_mem (.inr (.inl i))
      change mappedGroupNeighbors M A C.label (C.side.ladder.v (i.1+1))=_
      rw [fourIncidences_neighbors_tuple M hM (C.side.ladder.lower (i.1+1) hj hjn) A hmem C.label]
      simp only [Nat.add_sub_cancel,
        hpart,C.lower_prev_mem i,ite_true,C.label_upper (i.1+1) hj (by omega),
        C.lower_prev_label i]
      rw [show i.1+1+1=i.1+2 by omega,C.lower_next_contribution i]
      rfl

end CapPrefixData
end WaveTurbulence.Vine
