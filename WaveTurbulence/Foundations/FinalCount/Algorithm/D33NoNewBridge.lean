/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.LadderRestriction
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
public import WaveTurbulence.Foundations.FinalCount.Algorithm.RelationReroute
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ParallelBondAvoidance
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DisplayedBoundary
import Mathlib.Tactic

/-! # A continuing double rung creates no bridge

DH23 Appendix B algorithm remark one: the two boundary atoms remain joined
by two bonds, so every old path avoiding a retained bond can be rerouted
through the surviving rung while still avoiding that bond.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem d33_no_new_bridge (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hb : ∀ e : D,¬Degen.IsBridge M e)
    (hm : M.bondsBetween (r.vertex 3) (r.vertex 4) = 2) :
    ∀ e : Degen.RetainedDart M r.removedAtoms,¬Degen.IsBridge r.post e := by
  classical
  intro e
  have h3 := (mem_sdiff.mp (r.vertex_mem_post 3 (by decide) (by decide))).2
  have h4 := (mem_sdiff.mp (r.vertex_mem_post 4 (by decide) (by decide))).2
  have hm' : 2 ≤ r.post.bondsBetween (r.vertex 3) (r.vertex 4) := by
    have he : r.post.bondsBetween (r.vertex 3) (r.vertex 4) = M.bondsBetween (r.vertex 3) (r.vertex 4) :=
      Degen.bondsBetween_erase_eq M r.removedAtoms h3 h4
    rw [he,hm]
  let R := Degen.AdjWithoutBond r.post e
  have hret (x : D) (hx : M.atom x ∉ r.removedAtoms)
      (hy : M.atom (M.mate x) ∉ r.removedAtoms) (he : x ≠ e.val) (hme : x ≠ M.mate e.val) :
      Relation.EqvGen R (M.atom x) (M.atom (M.mate x)) := by
    apply Relation.EqvGen.rel
    refine ⟨⟨x,hx,hy⟩,rfl,rfl,?_,?_⟩
    · exact fun h => he (congrArg Subtype.val h)
    · exact fun h => hme (congrArg Subtype.val h)
  have hboundary (x : D) (hx : M.atom x ∈ r.removedAtoms)
      (hy : M.atom (M.mate x) ∉ r.removedAtoms) :
      Relation.EqvGen R (r.vertex 3) (M.atom (M.mate x)) := by
    obtain ⟨a,ha,hka,he⟩ := crossing_outer_displayed r x hx hy
    have hlabels : AppbPatternKind.d33.pattern.vertices \ AppbPatternKind.d33.pattern.removed = {3,4} := by decide
    have ha' : a = 3 ∨ a = 4 := by
      have hh := mem_sdiff.mpr ⟨ha,hka⟩
      rw [hlabels] at hh
      exact mem_insert.mp hh |>.imp_right mem_singleton.mp
    rw [he]
    rcases ha' with rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact parallel_bonds_path_without r.post e hm'
  have hp : Relation.EqvGen (Degen.AdjWithoutBond M e.val)
      (M.atom e.val) (M.atom (M.mate e.val)) := not_not.mp (hb e.val)
  have hh := reroute_path_in_relation M r.removedAtoms (r.vertex 3) R e.val hret hboundary hp
  have hpath : Relation.EqvGen R (r.post.atom e) (r.post.atom (r.post.mate e)) := by
    change Relation.EqvGen R (M.atom e.val) (M.atom (M.mate e.val))
    simpa only [rerouteAtom,e.property.1,e.property.2,ite_false] using hh
  exact fun h => h hpath

end WaveTurbulence.Mole.AppbAlgorithm
