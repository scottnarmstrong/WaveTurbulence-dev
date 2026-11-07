/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33NewReconstruction
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SpecialFigure
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SpecialFigureSwap
import Mathlib.Tactic

/-! # A special residual boundary pair forces the actual pre 3D3-6G figure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem d33new_of_residual_special_between_boundary (M : Molecule V D) (hno : AppbNoLoops M)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    {x : Degen.RetainedDart M r.removedAtoms} (hs : AppbSpecial r.post x)
    (he : r.post.ends x = s(r.vertex 3,r.vertex 4)) :
    ∃ q : AppbRealization M AppbPatternKind.d33new.pattern,
      q.vertex 1 = r.vertex 1 ∧ q.vertex 2 = r.vertex 2 ∧
      q.vertex 3 = r.vertex 3 ∧ q.vertex 4 = r.vertex 4 := by
  have hno' : AppbNoLoops r.post := fun x => hno x.val
  obtain ⟨t,ht1,ht2⟩ := special_bond_realization r.post hno' hs
  rcases Sym2.eq_iff.mp he with h | h
  · have h1 : t.vertex 1 = r.vertex 3 := ht1.trans h.1
    have h2 : t.vertex 2 = r.vertex 4 := ht2.trans h.2
    exact ⟨d33NewRealizationOfResidualSpecial M r t h1 h2,rfl,rfl,h1,h2⟩
  · have h1 : (swapSpecialFigure t).vertex 1 = r.vertex 3 :=
      (swapSpecialFigure_vertex_one t).trans (ht2.trans h.2)
    have h2 : (swapSpecialFigure t).vertex 2 = r.vertex 4 :=
      (swapSpecialFigure_vertex_two t).trans (ht1.trans h.1)
    exact ⟨d33NewRealizationOfResidualSpecial M r (swapSpecialFigure t) h1 h2,rfl,rfl,h1,h2⟩

/-- The actual negative figure test in rule three(c) excludes a special
bond between the two residual boundary atoms. -/
theorem no_residual_special_between_boundary_of_no_d33new (M : Molecule V D)
    (hno : AppbNoLoops M) (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hn : ¬∃ q : AppbRealization M AppbPatternKind.d33new.pattern,
      q.vertex 1 = r.vertex 1 ∧ q.vertex 2 = r.vertex 2 ∧
      q.vertex 3 = r.vertex 3 ∧ q.vertex 4 = r.vertex 4) :
    ∀ x : Degen.RetainedDart M r.removedAtoms,r.post.ends x = s(r.vertex 3,r.vertex 4) → ¬AppbSpecial r.post x :=
  fun x he hs => hn (d33new_of_residual_special_between_boundary M hno r hs he)

end WaveTurbulence.Mole.AppbAlgorithm
