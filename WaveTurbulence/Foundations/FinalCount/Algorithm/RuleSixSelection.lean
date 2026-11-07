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

/-- Both source alternatives give literal molecule-preserving progress. -/
theorem RuleSixSelection.progress {s : State.{u,v} V} (hM : s.graph.IsMolecule)
    {r : AppbRealization s.graph AppbPatternKind.r3.pattern} (h : RuleSixSelection s.graph r) :
    ∃ t : State.{u,v} V,GeometricStep s t ∧ t.graph.IsMolecule ∧ t.bondPotential < s.bondPotential := by
  cases h with
  | normal hn =>
    have hs := GeometricStep.delete s .r3 r
    exact ⟨ofMolecule r.post,hs,appb_eraseAtoms_isMolecule s.graph hM r.removedAtoms,hs.bondPotential_lt⟩
  | good t hc =>
    have hs := GeometricStep.r32 s r t
    have hM' := appb_eraseAtoms_isMolecule s.graph hM r.removedAtoms
    exact ⟨ofMolecule t.post,hs,appb_eraseAtoms_isMolecule r.post hM' t.removedAtoms,hs.bondPotential_lt⟩

end WaveTurbulence.Mole.AppbAlgorithm
