/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33DirectionBalance
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33RuleSelection
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DoublePairExistence
public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33LadderCharge
import Mathlib.Tactic

/-! # A terminal normal rung cannot leave a double boundary rung -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The source continuation/common-tail dichotomy follows from the actual
boundary multiplicity and degree-four orientation balance. -/
theorem d33_boundary_double_continues_or_common (M : Molecule V D) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (r : AppbRealization M AppbPatternKind.d33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4)
    (ho : AppbD33BoundaryOpposite M r)
    (hm : M.bondsBetween (r.vertex 3) (r.vertex 4) = 2) :
    D33Continues r ∨ HasD33ResidualCommon r := by
  have hm3 := r.vertex_mem_post 3 (by decide) (by decide)
  have hm4 := r.vertex_mem_post 4 (by decide) (by decide)
  have hn3 := (mem_sdiff.mp hm3).2
  have hn4 := (mem_sdiff.mp hm4).2
  have hd3 := r.post_vertex_degree 3 (by decide)
  have hd4 := r.post_vertex_degree 4 (by decide)
  rw [h3] at hd3
  rw [h4] at hd4
  have hd3' : r.post.deg (r.vertex 3) = 3 := by
    change r.post.deg (r.vertex 3)+1 = 4 at hd3
    omega
  have hd4' : r.post.deg (r.vertex 4) = 3 := by
    change r.post.deg (r.vertex 4)+1 = 4 at hd4
    omega
  have hne : r.vertex 3 ≠ r.vertex 4 := (r.vertex_eq_iff 3 4 (by decide) (by decide)).not.mpr (by decide)
  have hpost : r.post.bondsBetween (r.vertex 3) (r.vertex 4) = 2 :=
    (Degen.bondsBetween_erase_eq M r.removedAtoms hn3 hn4).trans hm
  rcases exists_double_pair_realization r.post (fun x => hno x.val) hm3 hm4 hne hd3' hd4' hpost with h | h
  · obtain ⟨t,h1,h2⟩ := h
    exact Or.inl ⟨t,Or.inl ⟨h1,h2⟩,d33_next_boundary_opposite M hM r t h3 h4 ho h1 h2⟩
  · obtain ⟨t,h1,h2⟩ := h
    exact Or.inr ⟨t,Or.inl ⟨h1,h2⟩⟩

theorem d33_terminal_boundary_not_double (M : Molecule V D) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (r : AppbRealization M AppbPatternKind.d33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4)
    (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r)
    (ht : ¬HasD33ResidualCommon r) : M.bondsBetween (r.vertex 3) (r.vertex 4) ≠ 2 := by
  intro hm
  exact (d33_boundary_double_continues_or_common M hM hno r h3 h4 ho hm).elim hc ht

/-- At source rule three(c)(iii), the active link potential loses exactly
two. The next component scan must pay for this rung; it is not an
unbounded hidden sequence of normal D33 operations. -/
theorem d33_terminal_activePotential_change (M : Molecule V D) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (r : AppbRealization M AppbPatternKind.d33.pattern)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4)
    (ho : AppbD33BoundaryOpposite M r) (hc : ¬D33Continues r)
    (ht : ¬HasD33ResidualCommon r) : activeLinkPotential r.post = activeLinkPotential M-2 := by
  rw [d33_normal_activePotential_change_by_rung M hM r h3 h4 ho,
    if_neg (d33_terminal_boundary_not_double M hM hno r h3 h4 ho hc ht)]

end WaveTurbulence.Mole.AppbAlgorithm
