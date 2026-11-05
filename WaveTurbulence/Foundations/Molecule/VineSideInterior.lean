/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineSelectedAtoms
public import WaveTurbulence.Foundations.Molecule.VineSideLabels
public import WaveTurbulence.Foundations.Molecule.VineCapBijection
public import WaveTurbulence.Foundations.Molecule.VineCoreAtoms
import Mathlib.Tactic

/-! # The interior deleted from a complete type-VII side block -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The two side joints have exactly the old labels 7 and 8. -/
theorem VineRealization.mem_side_joints_iff {M : Molecule V D} {S : Finset V} {a b : V}
    (R : VineRealization M .VII S a b) {v : V} (hv : v ∈ S) :
    v ∈ ({(R.coreAtom (7 : Fin 11)).1,(R.coreAtom (8 : Fin 11)).1} : Finset V) ↔
      R.f v=7 ∨ R.f v=8 := by
  simp only [mem_insert,mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl (R.label_coreAtom (7 : Fin 11))
    · exact Or.inr (R.label_coreAtom (8 : Fin 11))
  · rintro (h | h)
    · exact Or.inl (R.injOn hv (R.coreAtom (7 : Fin 11)).2
        (h.trans (R.label_coreAtom (7 : Fin 11)).symm))
    · exact Or.inr (R.injOn hv (R.coreAtom (8 : Fin 11)).2
        (h.trans (R.label_coreAtom (8 : Fin 11)).symm))

/-- Removing the full side retains its two old joints 7 and 8. The
removed interior consists exactly of the triangle and the cyan allocation. -/
theorem VineRealization.side_interior_eq {M : Molecule V D} {S : Finset V} {a b : V}
    (R : VineRealization M .VII S a b) (N k : ℕ) (hN : 11 ≤ N) :
    R.selectedAtoms (sideLabels N k) \
      {(R.coreAtom (7 : Fin 11)).1,(R.coreAtom (8 : Fin 11)).1}=
        R.selectedAtoms (capLabels N k) := by
  ext v
  constructor
  · intro hv
    have hh := mem_sdiff.mp hv
    have hm := mem_filter.mp hh.1
    apply mem_filter.mpr
    refine ⟨hm.1,?_⟩
    have hj := (R.mem_side_joints_iff hm.1).not.mp hh.2
    have hl := (mem_sideLabels_iff N k (R.f v)).mp hm.2
    rw [mem_capLabels_iff]
    rcases hl with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact False.elim (hj (Or.inl h))
    · exact False.elim (hj (Or.inr h))
    · exact Or.inr (Or.inr (Or.inr h))
  · intro hv
    have hm := mem_filter.mp hv
    have hl := (mem_capLabels_iff N k (R.f v)).mp hm.2
    have hj : ¬(R.f v=7 ∨ R.f v=8) := by
      rcases hl with h | h | h | h <;> omega
    apply mem_sdiff.mpr
    constructor
    · apply mem_filter.mpr
      refine ⟨hm.1,?_⟩
      rw [mem_sideLabels_iff]
      rcases hl with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact (R.mem_side_joints_iff hm.1).not.mpr hj

end WaveTurbulence.Vine
