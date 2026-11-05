/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineProtectedCoreBackbones
public import WaveTurbulence.Foundations.Molecule.VineSideInterior
import Mathlib.Tactic

/-! # The retained type-VII core edges avoid the removed side -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- Literal protected VII edges avoid the triangle and are not internal
to the five old side labels. This is a finite source-edge certificate. -/
theorem protectedVII_core_certificate :
    ∀ e ∈ protectedCoreBonds .VII {4,5,6,7,8},e.1<11 ∧ e.2<11 ∧
      e.1 ∉ ({4,5,6} : Finset ℕ) ∧ e.2 ∉ ({4,5,6} : Finset ℕ) ∧
      ¬(e.1 ∈ ({4,5,6,7,8} : Finset ℕ) ∧ e.2 ∈ ({4,5,6,7,8} : Finset ℕ)) := by decide

/-- The old protected edges remain outside the full expanded cyan side,
whose fresh allocation begins at N≥11. -/
theorem protectedVII_core_labels (N k : ℕ) (hN : 11 ≤ N) (e : ℕ×ℕ)
    (he : e ∈ protectedCoreBonds .VII {4,5,6,7,8}) :
    e.1 ∉ capLabels N k ∧ e.2 ∉ capLabels N k ∧
      ¬(e.1 ∈ sideLabels N k ∧ e.2 ∈ sideLabels N k) := by
  have hh := protectedVII_core_certificate e he
  simp only [mem_insert,mem_singleton] at hh
  simp only [mem_capLabels_iff,mem_sideLabels_iff]
  omega

variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Literal protected VII edges supply primitive actual avoidance facts. -/
theorem VineRealization.protectedVII_core_atoms {M : Molecule V D}
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b)
    (N k : ℕ) (hN : 11 ≤ N) (i j : Fin 11)
    (he : (i.1,j.1) ∈ protectedCoreBonds .VII {4,5,6,7,8}) :
    (R.coreAtom i).1 ∉ R.selectedAtoms (sideLabels N k) \
      {(R.coreAtom (7 : Fin 11)).1,(R.coreAtom (8 : Fin 11)).1} ∧
    (R.coreAtom j).1 ∉ R.selectedAtoms (sideLabels N k) \
      {(R.coreAtom (7 : Fin 11)).1,(R.coreAtom (8 : Fin 11)).1} ∧
    ¬((R.coreAtom i).1 ∈ R.selectedAtoms (sideLabels N k) ∧
      (R.coreAtom j).1 ∈ R.selectedAtoms (sideLabels N k)) := by
  have hh := protectedVII_core_labels N k hN (i.1,j.1) he
  rw [R.side_interior_eq N k hN]
  constructor
  · intro hm
    have hm' := (mem_filter.mp hm).2
    rw [R.label_coreAtom i] at hm'
    exact hh.1 hm'
  constructor
  · intro hm
    have hm' := (mem_filter.mp hm).2
    rw [R.label_coreAtom j] at hm'
    exact hh.2.1 hm'
  · intro hm
    apply hh.2.2
    constructor
    · have hm' := (mem_filter.mp hm.1).2
      simpa only [R.label_coreAtom i] using hm'
    · have hm' := (mem_filter.mp hm.2).2
      simpa only [R.label_coreAtom j] using hm'

end WaveTurbulence.Vine
