/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPatternMultiplicities
public import WaveTurbulence.Foundations.FinalCount.AppBLinkNeighbors
import Mathlib.Tactic

/-! # Exact neighbour table of the deleted degree-three double pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_d33_internal_multiplicity (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) :
    M.bondsBetween (r.vertex 1) (r.vertex 2) = 2 :=
  (r.bondsBetween_vertices_eq 1 2 (by decide) (by decide)).trans (by decide)

/-- The sole single-rail neighbour of vertex 1 is displayed vertex 3. -/
theorem appb_d33_single_neighbor_1 (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) (c : V)
    (hc : M.bondsBetween (r.vertex 1) c = 1) : c = r.vertex 3 := by
  obtain ⟨b,hb,rfl⟩ := r.neighbor_mem_vertices 1 (by decide) (by rw [hc]; norm_num)
  have hm : AppbPatternKind.d33.pattern.multiplicity 1 b = 1 :=
    (r.bondsBetween_vertices_eq 1 b (by decide) hb).symm.trans hc
  rw [show AppbPatternKind.d33.pattern.vertices = ({1,2,3,4} : Finset ℕ) by decide] at hb
  simp only [mem_insert,mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · have hh : AppbPatternKind.d33.pattern.multiplicity 1 1 = 0 := by decide
    rw [hh] at hm
    omega
  · have hh : AppbPatternKind.d33.pattern.multiplicity 1 2 = 2 := by decide
    rw [hh] at hm
    omega
  · rfl
  · have hh : AppbPatternKind.d33.pattern.multiplicity 1 4 = 0 := by decide
    rw [hh] at hm
    omega

/-- The sole single-rail neighbour of vertex 2 is displayed vertex 4. -/
theorem appb_d33_single_neighbor_2 (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) (c : V)
    (hc : M.bondsBetween (r.vertex 2) c = 1) : c = r.vertex 4 := by
  obtain ⟨b,hb,rfl⟩ := r.neighbor_mem_vertices 2 (by decide) (by rw [hc]; norm_num)
  have hm : AppbPatternKind.d33.pattern.multiplicity 2 b = 1 :=
    (r.bondsBetween_vertices_eq 2 b (by decide) hb).symm.trans hc
  rw [show AppbPatternKind.d33.pattern.vertices = ({1,2,3,4} : Finset ℕ) by decide] at hb
  simp only [mem_insert,mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · have hh : AppbPatternKind.d33.pattern.multiplicity 2 1 = 2 := by decide
    rw [hh] at hm
    omega
  · have hh : AppbPatternKind.d33.pattern.multiplicity 2 2 = 0 := by decide
    rw [hh] at hm
    omega
  · have hh : AppbPatternKind.d33.pattern.multiplicity 2 3 = 0 := by decide
    rw [hh] at hm
    omega
  · rfl

end WaveTurbulence.Mole
