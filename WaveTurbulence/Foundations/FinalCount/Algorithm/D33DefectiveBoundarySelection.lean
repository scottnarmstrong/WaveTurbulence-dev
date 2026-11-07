/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33ContinuationInvariants
public import WaveTurbulence.Foundations.FinalCount.Algorithm.PatternReachability
import Mathlib.Tactic

/-! # A defective next boundary forces the good residual-defect branch

This is the actual graph implication used to charge a possible special
bond increase in the preceding normal ladder step to its next good step.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem HasD33New.boundary_four {M : Molecule V D}
    {r : AppbRealization M AppbPatternKind.d33.pattern} (h : HasD33New r) :
    M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 4) = 4 := by
  obtain ⟨t,h1,h2,h3,h4⟩ := h
  have hd3 : M.deg (t.vertex 3) = 4 := (t.deleted_degree 3 (by decide)).trans (by decide)
  have hd4 : M.deg (t.vertex 4) = 4 := (t.deleted_degree 4 (by decide)).trans (by decide)
  rw [h3] at hd3
  rw [h4] at hd4
  exact ⟨hd3,hd4⟩

/-- Every other primary case requires both boundary atoms to have degree
four. Thus the failed boundary test forces exactly the source's residual
component-defect alternative, before either decoration branch is chosen. -/
theorem d33_defective_boundary_tests (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hd : ¬(M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 4) = 4)) :
    ¬D33Continues r ∧ ¬HasD33New r ∧ ¬HasD33ResidualCommon r ∧ HasD33ComponentDefect r := by
  refine ⟨fun h => hd h.boundary_four,fun h => hd h.boundary_four,fun h => hd h.boundary_four,?_⟩
  have hw (a : ℕ) (ha : a ∈ AppbPatternKind.d33.pattern.vertices)
      (hka : a ∉ AppbPatternKind.d33.pattern.removed) (hda : M.deg (r.vertex a) ≠ 4) :
      HasD33ComponentDefect r := by
    refine ⟨r.vertex a,r.vertex_mem a ha,all_realized_vertices_connected M .d33 r a ha,?_,hda⟩
    intro h
    exact hka ((r.vertex_mem_removed_iff a ha).mp h)
  rcases not_and_or.mp hd with hd | hd
  · exact hw 3 (by decide) (by decide) hd
  · exact hw 4 (by decide) (by decide) hd

theorem d33_defective_boundary_selection (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) (ho : AppbD33BoundaryOpposite M r)
    (hd : ¬(M.deg (r.vertex 3) = 4 ∧ M.deg (r.vertex 4) = 4)) : D33RuleSelection M r := by
  obtain ⟨hc,hn,ht,hdef⟩ := d33_defective_boundary_tests M r hd
  exact .residualDefect ho hc hn ht hdef

end WaveTurbulence.Mole.AppbAlgorithm
