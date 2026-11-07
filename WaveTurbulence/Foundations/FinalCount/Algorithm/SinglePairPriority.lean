/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SinglePairExistence
import Mathlib.Tactic

/-! # The global preference for the six new figures in source rule two -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def NewSinglePairFigure (M : Molecule V D) : Prop :=
  ∃ k ∈ ([AppbPatternKind.s33new1,.s33new2,.s33new3,.s33new4,.s33new5,.s33new6] : List _),
    Nonempty (AppbRealization M k.pattern)

/-- The primary figure is selected only after the absence of new figures
has been tested throughout the molecule, as required by rule two(a). -/
inductive RuleTwoFigure (M : Molecule V D) : Prop
  | newFigure (h : NewSinglePairFigure M) : RuleTwoFigure M
  | primary (hnew : ¬NewSinglePairFigure M)
      (r : AppbRealization M AppbPatternKind.s33.pattern) : RuleTwoFigure M

theorem rule_two_figure (M : Molecule V D) (h : SinglePairFigure M) : RuleTwoFigure M := by
  classical
  by_cases hn : NewSinglePairFigure M
  · exact .newFigure hn
  · obtain ⟨k,hk,⟨r⟩⟩ := h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .primary hn r
    all_goals exact (hn ⟨_,by simp,⟨r⟩⟩).elim

end WaveTurbulence.Mole.AppbAlgorithm
