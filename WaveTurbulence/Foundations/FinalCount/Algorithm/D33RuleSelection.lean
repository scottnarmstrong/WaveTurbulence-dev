/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33Continuation
import Mathlib.Tactic

/-! # The ordered geometric tests in source rule three(b)--(c)

These tests precede the decoration partition. This module does not assert
that an untested primary figure is normal or supply an analytic bound.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The original four-center good figure, with the current head fixed. -/
def HasD33New {M : Molecule V D} (r : AppbRealization M AppbPatternKind.d33.pattern) : Prop :=
  ∃ q : AppbRealization M AppbPatternKind.d33new.pattern,
    q.vertex 1 = r.vertex 1 ∧ q.vertex 2 = r.vertex 2 ∧
    q.vertex 3 = r.vertex 3 ∧ q.vertex 4 = r.vertex 4

/-- The common-tail good figure remaining after the current head is removed. -/
def HasD33ResidualCommon {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) : Prop :=
  ∃ t : AppbRealization r.post AppbPatternKind.d33same.pattern,
    (t.vertex 1 = r.vertex 3 ∧ t.vertex 2 = r.vertex 4) ∨
    (t.vertex 1 = r.vertex 4 ∧ t.vertex 2 = r.vertex 3)

/-- The degree test is restricted to the old component being scanned. -/
def HasD33ComponentDefect {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) : Prop :=
  ∃ b ∈ M.atoms,M.SameComponent (r.vertex 1) b ∧ b ∉ r.removedAtoms ∧ M.deg b ≠ 4

inductive D33RuleSelection (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) : Prop
  | wrongDirections (h : ¬AppbD33BoundaryOpposite M r) : D33RuleSelection M r
  | continuing (ho : AppbD33BoundaryOpposite M r) (h : D33Continues r) : D33RuleSelection M r
  | newFigure (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r)
      (h : HasD33New r) : D33RuleSelection M r
  | residualCommon (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r)
      (hn : ¬HasD33New r) (h : HasD33ResidualCommon r) : D33RuleSelection M r
  | residualDefect (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r)
      (hn : ¬HasD33New r) (ht : ¬HasD33ResidualCommon r)
      (h : HasD33ComponentDefect r) : D33RuleSelection M r
  | terminalRung (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r)
      (hn : ¬HasD33New r) (ht : ¬HasD33ResidualCommon r)
      (h : ∀ b ∈ M.atoms,M.SameComponent (r.vertex 1) b → b ∉ r.removedAtoms → M.deg b = 4) :
      D33RuleSelection M r

/-- DH23 Appendix B rule three's geometric decisions are exhaustive and
retain each preceding negative test. -/
theorem exists_d33_rule_selection (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern) : D33RuleSelection M r := by
  classical
  by_cases ho : AppbD33BoundaryOpposite M r
  · by_cases hc : D33Continues r
    · exact .continuing ho hc
    · by_cases hn : HasD33New r
      · exact .newFigure ho hc hn
      · by_cases ht : HasD33ResidualCommon r
        · exact .residualCommon ho hc hn ht
        · by_cases hd : HasD33ComponentDefect r
          · exact .residualDefect ho hc hn ht hd
          · exact .terminalRung ho hc hn ht (fun b hb hp hr => by
              by_contra h
              exact hd ⟨b,hb,hp,hr,h⟩)
  · exact .wrongDirections ho

/-- The component-local defect is sufficient for the source reinsertion
operation's non-saturation premise, stated globally in the G4 API. -/
theorem HasD33ComponentDefect.residualDefect {M : Molecule V D}
    {r : AppbRealization M AppbPatternKind.d33.pattern} (h : HasD33ComponentDefect r) :
    AppbD33ResidualDefect M r := by
  obtain ⟨b,hb,hc,hr,hd⟩ := h
  refine ⟨b,hb,?_,?_,hd⟩
  · intro he
    exact hr (he ▸ Finset.mem_image_of_mem r.vertex (by decide : 1 ∈ AppbPatternKind.d33.pattern.removed))
  · intro he
    exact hr (he ▸ Finset.mem_image_of_mem r.vertex (by decide : 2 ∈ AppbPatternKind.d33.pattern.removed))

end WaveTurbulence.Mole.AppbAlgorithm
