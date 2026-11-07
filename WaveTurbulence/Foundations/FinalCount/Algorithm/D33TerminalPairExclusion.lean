/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33DoubleContinuation
import Mathlib.Tactic

/-! # The terminal component scan has no degree-three double pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Source remark three's exclusion is for every actual pair in the
scanned component, not merely the currently labeled boundary pair. -/
theorem d33_terminal_no_degree_three_double_in_component (M : Molecule V D) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (r : AppbRealization M AppbPatternKind.d33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4)
    (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r)
    (ht : ¬HasD33ResidualCommon r)
    (hregular : ∀ b ∈ M.atoms,M.SameComponent (r.vertex 1) b → b ∉ r.removedAtoms → M.deg b = 4)
    {a b : V} (ha : a ∈ r.post.atoms) (hb : b ∈ r.post.atoms)
    (hca : M.SameComponent (r.vertex 1) a) (hda : r.post.deg a = 3) (hdb : r.post.deg b = 3)
    (hab : a ≠ b) : r.post.bondsBetween a b ≠ 2 := by
  intro hm
  obtain ⟨x,hx,hy⟩ := Degen.adj_of_bondsBetween_pos r.post hab (by rw [hm]; decide)
  have hcb := Relation.EqvGen.trans _ _ _ hca (Relation.EqvGen.rel _ _
    (show M.Adj a b from ⟨x.val,hx,hy⟩))
  have hA := d33_terminal_degree_three M r hregular ha hca hda
  have hB := d33_terminal_degree_three M r hregular hb hcb hdb
  have hn3 := (mem_sdiff.mp (r.vertex_mem_post 3 (by decide) (by decide))).2
  have hn4 := (mem_sdiff.mp (r.vertex_mem_post 4 (by decide) (by decide))).2
  have hnot : r.post.bondsBetween (r.vertex 3) (r.vertex 4) ≠ 2 := by
    intro hh
    exact d33_terminal_boundary_not_double M hM hno r h3 h4 ho hc ht
      ((Degen.bondsBetween_erase_eq M r.removedAtoms hn3 hn4).symm.trans hh)
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact hab (hA.trans hB.symm)
  · rw [hA,hB] at hm
    exact hnot hm
  · rw [hA,hB,bondsBetween_symm r.post (r.vertex 4) (r.vertex 3)] at hm
    exact hnot hm
  · exact hab (hA.trans hB.symm)

end WaveTurbulence.Mole.AppbAlgorithm
