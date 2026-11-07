/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.GlobalSmallBoundaryEffects
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GlobalClosedTableEffects
public import WaveTurbulence.Foundations.FinalCount.AppBNormalDegreeEffects
import Mathlib.Tactic

/-! # Global nu increments in the normal and fine small-cut families -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem d33_global_nu_change (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e) : appbNu r.post-appbNu M = 0 := by
  have hh := (global_small_boundary_graph_effects M .d33 (by decide) r hbridge (by decide) (by decide)).2.2
  norm_num only [show AppbPatternKind.d33.pattern.removed.card = 2 by decide,
    show AppbPatternKind.d33.pattern.edges.length = 4 by decide] at hh
  exact hh

theorem r3_global_nu_change (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e) : appbNu r.post-appbNu M = 2 := by
  have hh := (global_small_boundary_graph_effects M .r3 (by decide) r hbridge (by decide) (by decide)).2.2
  norm_num only [show AppbPatternKind.r3.pattern.removed.card = 1 by decide,
    show AppbPatternKind.r3.pattern.edges.length = 3 by decide] at hh
  exact hh

theorem r21_global_nu_change (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r21.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e) : appbNu r.post-appbNu M = 0 := by
  have hh := (global_small_boundary_graph_effects M .r21 (by decide) r hbridge (by decide) (by decide)).2.2
  norm_num only [show AppbPatternKind.r21.pattern.removed.card = 1 by decide,
    show AppbPatternKind.r21.pattern.edges.length = 2 by decide] at hh
  exact hh

theorem r22_global_nu_change (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r22.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e) : appbNu r.post-appbNu M = 0 := by
  have hh := (global_small_boundary_graph_effects M .r22 (by decide) r hbridge (by decide) (by decide)).2.2
  norm_num only [show AppbPatternKind.r22.pattern.removed.card = 1 by decide,
    show AppbPatternKind.r22.pattern.edges.length = 2 by decide] at hh
  exact hh

theorem r23_global_nu_change (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r23.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e) : appbNu r.post-appbNu M = (-4) := by
  have hh := (global_small_boundary_graph_effects M .r23 (by decide) r hbridge (by decide) (by decide)).2.2
  norm_num only [show AppbPatternKind.r23.pattern.removed.card = 3 by decide,
    show AppbPatternKind.r23.pattern.edges.length = 4 by decide] at hh
  exact hh

theorem d33_normal_global_statistics (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4) :
    appbNu r.post-appbNu M = 0 ∧
      ((appbDegreeAtoms r.post 3).card : ℤ)-(appbDegreeAtoms M 3).card = 0 :=
  ⟨d33_global_nu_change M r hbridge,appb_d33_normal_degreeThree M r h3 h4⟩

theorem r3_normal_global_statistics (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e)
    (h2 : M.deg (r.vertex 2) = 4) (h3 : M.deg (r.vertex 3) = 4)
    (h4 : M.deg (r.vertex 4) = 4) :
    appbNu r.post-appbNu M = 2 ∧
      ((appbDegreeAtoms r.post 3).card : ℤ)-(appbDegreeAtoms M 3).card = 2 :=
  ⟨r3_global_nu_change M r hbridge,appb_r3_normal_degreeThree M r h2 h3 h4⟩

theorem common_removed_center_incidence : ∀ a ∈ appbR23Common.removed,
    a = 1 ∨ ∃ i : Fin appbR23Common.edges.length,
      appbR23Common.edges[i] = (1,a) ∨ appbR23Common.edges[i] = (a,1) := by decide

theorem r23common_global_nu_change (M : Molecule V D)
    (r : AppbRealization M appbR23Common)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e) : appbNu r.post-appbNu M = -4 := by
  have hbound : (Degen.boundaryDarts M r.removedAtoms).card ≤ 3 := by
    rw [r.boundary_card]
    decide
  have hnon : (Degen.boundaryDarts M r.removedAtoms).Nonempty := Finset.card_pos.mp (by
    rw [r.boundary_card]
    decide)
  have hf : r.post.numComponents = M.numComponents :=
    numComponents_eraseAtoms_eq_of_small_boundary M r.removedAtoms hbridge hbound hnon
      (FigurePaths.removed_connected_of_center_incidence r common_removed_center_incidence)
  rw [r.post_nu,hf]
  norm_num [appbR23Common]

end WaveTurbulence.Mole.AppbAlgorithm
