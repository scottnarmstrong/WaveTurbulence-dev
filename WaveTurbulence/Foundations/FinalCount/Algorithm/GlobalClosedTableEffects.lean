/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedDeletionComponents
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GlobalSmallBoundaryEffects
import Mathlib.Tactic

/-! # Whole-component fine removals retain their global graph effects -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem global_closed_table_graph_effects (M : Molecule V D) (P : AppbPattern)
    (r : AppbRealization M P) (h1 : 1 ∈ P.removed) (hzero : P.boundaryCount = 0)
    (hstar : ∀ a ∈ P.removed,a = 1 ∨ ∃ i : Fin P.edges.length,
      P.edges[i] = (1,a) ∨ P.edges[i] = (a,1)) :
    r.post.numComponents+1 = M.numComponents ∧
    r.post.circuitRank-M.circuitRank = -(P.edges.length : ℤ)+P.removed.card-1 ∧
    appbNu r.post-appbNu M = -4*(P.removed.card : ℤ)+2*P.edges.length+4 := by
  have hboundary : Degen.boundaryDarts M r.removedAtoms = ∅ := by
    apply card_eq_zero.mp
    rw [r.boundary_card,hzero]
  have hm : r.vertex 1 ∈ r.removedAtoms := mem_image_of_mem _ h1
  have hconn := FigurePaths.removed_connected_of_center_incidence r hstar
  have hf : r.post.numComponents+1 = M.numComponents :=
    numComponents_erase_closed_component M r.removedAtoms hboundary hm (r.vertex_mem 1 (mem_union_left _ h1))
      (fun c hc => hconn c hc _ hm)
  have hfz : (r.post.numComponents : ℤ)+1 = M.numComponents := by exact_mod_cast hf
  refine ⟨hf,?_,?_⟩
  · rw [r.post_circuitRank]
    omega
  · rw [r.post_nu]
    omega

/-- DH23 2R-4F, including arbitrary untouched components. -/
theorem r24_global_nu_change (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r24.pattern) : appbNu r.post-appbNu M = 0 := by
  have hh := global_closed_table_graph_effects M _ r (by decide) (by decide)
    (patterns_removed_center_incidence .r24 (by decide))
  norm_num only [show AppbPatternKind.r24.pattern.removed.card = 2 by decide,
    show AppbPatternKind.r24.pattern.edges.length = 2 by decide] at hh
  exact hh.2.2

/-- The closed triangle in 2R-3F has nu decrement two, also globally. -/
theorem r23triangle_global_nu_change (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r23triangle.pattern) : appbNu r.post-appbNu M = -2 := by
  have hh := global_closed_table_graph_effects M _ r (by decide) (by decide)
    (patterns_removed_center_incidence .r23triangle (by decide))
  norm_num only [show AppbPatternKind.r23triangle.pattern.removed.card = 3 by decide,
    show AppbPatternKind.r23triangle.pattern.edges.length = 3 by decide] at hh
  exact hh.2.2

end WaveTurbulence.Mole.AppbAlgorithm
