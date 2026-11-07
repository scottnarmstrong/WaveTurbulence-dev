/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33TerminalSpecial
public import WaveTurbulence.Foundations.FinalCount.AppBBranchConditions
import Mathlib.Tactic

/-! # Actual next-rung geometry and the component scan at the end of a ladder -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The residual rung has two distinct single-rail neighbours, with
opposite directions. Both orientations of its two centers are allowed. -/
def D33Continues {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) : Prop :=
  ∃ t : AppbRealization r.post AppbPatternKind.d33.pattern,
    ((t.vertex 1 = r.vertex 3 ∧ t.vertex 2 = r.vertex 4) ∨
     (t.vertex 1 = r.vertex 4 ∧ t.vertex 2 = r.vertex 3)) ∧
    AppbD33BoundaryOpposite r.post t

/-- The only possible residual degree-three atoms in the scanned old
component are the two displayed boundary atoms. -/
theorem d33_terminal_degree_three (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hregular : ∀ b ∈ M.atoms, M.SameComponent (r.vertex 1) b →
      b ∉ r.removedAtoms → M.deg b = 4)
    {b : V} (hb : b ∈ r.post.atoms) (hc : M.SameComponent (r.vertex 1) b)
    (hd : r.post.deg b = 3) : b = r.vertex 3 ∨ b = r.vertex 4 := by
  by_cases hi : b ∈ AppbPatternKind.d33.pattern.vertices.image r.vertex
  · exact D33Special.displayed_survivor r hb hi
  · have h4 := hregular b (mem_sdiff.mp hb).1 hc (mem_sdiff.mp hb).2
    have he := r.post_degree_outside b hi
    omega

/-- Source remark three: after a failed continuation test, the scan in
this component cannot select another opposite-rail primary double pair.
The statement concerns actual residual figures, not stored step counts. -/
theorem no_next_primary_d33_of_not_continues (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hregular : ∀ b ∈ M.atoms, M.SameComponent (r.vertex 1) b →
      b ∉ r.removedAtoms → M.deg b = 4) (hn : ¬D33Continues r)
    (t : AppbRealization r.post AppbPatternKind.d33.pattern)
    (hc : M.SameComponent (r.vertex 1) (t.vertex 1)) :
    ¬AppbD33BoundaryOpposite r.post t := by
  intro hopp
  have hpath : M.SameComponent (t.vertex 1) (t.vertex 2) := by
    have hp := realized_edge_adj t (0 : Fin 4)
    obtain ⟨x,hx,hy⟩ := hp
    exact Relation.EqvGen.rel _ _ ⟨x.val,hx,hy⟩
  have hc2 := Relation.EqvGen.trans _ _ _ hc hpath
  have hd1 : r.post.deg (t.vertex 1) = 3 :=
    (t.deleted_degree 1 (by decide)).trans (by decide)
  have hd2 : r.post.deg (t.vertex 2) = 3 :=
    (t.deleted_degree 2 (by decide)).trans (by decide)
  have h1 := d33_terminal_degree_three M r hregular (t.vertex_mem 1 (by decide)) hc hd1
  have h2 := d33_terminal_degree_three M r hregular (t.vertex_mem 2 (by decide)) hc2 hd2
  have hne : t.vertex 1 ≠ t.vertex 2 :=
    (t.vertex_eq_iff 1 2 (by decide) (by decide)).not.mpr (by decide)
  apply hn
  refine ⟨t,?_,hopp⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact (hne (h1.trans h2.symm)).elim
  · exact Or.inl ⟨h1,h2⟩
  · exact Or.inr ⟨h1,h2⟩
  · exact (hne (h1.trans h2.symm)).elim

end WaveTurbulence.Mole.AppbAlgorithm
