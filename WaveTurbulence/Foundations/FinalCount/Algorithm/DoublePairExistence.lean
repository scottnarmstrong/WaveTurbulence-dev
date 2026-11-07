/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.DoublePairPatterns
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # Rule three always has one of the two actual double-pair figures -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 Appendix B rule three's geometric dichotomy, before direction
and decoration tests: distinct boundary atoms, or a common boundary atom. -/
theorem exists_double_pair_realization (M : Molecule V D) (hno : AppbNoLoops M)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : a ≠ b)
    (hda : M.deg a = 3) (hdb : M.deg b = 3) (hm : M.bondsBetween a b = 2) :
    (∃ r : AppbRealization M AppbPatternKind.d33.pattern,r.vertex 1 = a ∧ r.vertex 2 = b) ∨
    (∃ r : AppbRealization M AppbPatternKind.d33same.pattern,r.vertex 1 = a ∧ r.vertex 2 = b) := by
  classical
  obtain ⟨x,hx,c,hc,hca,hcb,hex⟩ := exists_boundary_neighbor M hno hda hm
  have hm' : M.bondsBetween b a = 2 := (bondsBetween_symm M b a).trans hm
  obtain ⟨y,hy,d,hd,hdb',hda',hey⟩ := exists_boundary_neighbor M hno hdb hm'
  let e := doublePairEdges M hab hcb hda' hm hx hy hex hey
  by_cases hcd : c = d
  · subst d
    exact Or.inr ⟨commonDoublePairRealization M ha hb hc hab hca hcb hda hdb e,rfl,rfl⟩
  · exact Or.inl ⟨distinctDoublePairRealization M ha hb hc hd hab hca hcb hda' hdb' hcd hda hdb e,rfl,rfl⟩

end WaveTurbulence.Mole.AppbAlgorithm
