/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SpecialFigure
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GeometricStep
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionMolecule
import Mathlib.Tactic

/-! # Actual special-bond selection in source rule six -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
universe u v
variable {V : Type v} [DecidableEq V]
variable {D : Type u} [Fintype D] [DecidableEq D]

/-- The source component is the old component of the removed degree-three
atom. Tests in unrelated components do not alter this branch selection. -/
inductive RuleSixSelection (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern) : Prop
  | normal (hn : ∀ x : Degen.RetainedDart M r.removedAtoms,
      M.SameComponent (r.vertex 1) (M.atom x.val) → ¬AppbSpecial r.post x) : RuleSixSelection M r
  | good (t : AppbRealization r.post AppbPatternKind.s33new3.pattern)
      (hc : M.SameComponent (r.vertex 1) (t.vertex 1)) : RuleSixSelection M r

/-- DH23 Appendix B rule six's special-bond decision produces the actual
residual group in the good case. -/
theorem exists_rule_six_selection (M : Molecule V D) (hno : AppbNoLoops M)
    (r : AppbRealization M AppbPatternKind.r3.pattern) : RuleSixSelection M r := by
  classical
  by_cases hn : ∃ x : Degen.RetainedDart M r.removedAtoms,
      M.SameComponent (r.vertex 1) (M.atom x.val) ∧ AppbSpecial r.post x
  · obtain ⟨x,hc,hs⟩ := hn
    have hno' : AppbNoLoops r.post := fun x => hno x.val
    obtain ⟨t,h1,h2⟩ := special_bond_realization r.post hno' hs
    exact .good t (h1.symm ▸ hc)
  · exact .normal (fun x hc hs => hn ⟨x,hc,hs⟩)

end WaveTurbulence.Mole.AppbAlgorithm
