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

end WaveTurbulence.Mole.AppbAlgorithm
