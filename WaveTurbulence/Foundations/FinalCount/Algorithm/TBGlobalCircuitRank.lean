/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.SingletonBoundaryComponents
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GlobalClosedTableEffects
import Mathlib.Tactic

/-! # Both TB circuit-rank effects with untouched components present -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem tb1_global_circuitRank (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.tb1.pattern) :
    M.circuitRank = r.post.circuitRank+2 := by
  have hh := global_closed_table_graph_effects M _ r (by decide) (by decide)
    (patterns_removed_center_incidence .tb1 (by decide))
  have he : AppbPatternKind.tb1.pattern.edges.length = 3 := rfl
  have hr : AppbPatternKind.tb1.pattern.removed.card = 2 := by decide
  rw [he,hr] at hh
  omega

theorem tb2_global_circuitRank (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.tb2.pattern) :
    M.circuitRank = r.post.circuitRank+2 := by
  have hcard : (Degen.boundaryDarts M r.removedAtoms).card = 1 := by
    rw [r.boundary_card]
    decide
  have hf : r.post.numComponents = M.numComponents := numComponents_erase_single_boundary M r.removedAtoms hcard
    (FigurePaths.removed_connected_of_center_incidence r (patterns_removed_center_incidence .tb2 (by decide)))
  have hh := r.post_circuitRank
  have he : AppbPatternKind.tb2.pattern.edges.length = 4 := rfl
  have hr : AppbPatternKind.tb2.pattern.removed.card = 2 := by decide
  rw [he,hr,hf] at hh
  omega

end WaveTurbulence.Mole.AppbAlgorithm
