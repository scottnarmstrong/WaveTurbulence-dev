/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTwoBoundaryConnectivity
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
import Mathlib.Tactic

/-! # 3S3New scenarios 4 and 6: exact residual connectivity -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Scenario 4 leaves only one displayed survivor, so every ambient
survivor is in that same component. -/
theorem appb_s33new4_post_connected (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new4.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) :
    ∀ v ∈ r.post.atoms, ∀ w ∈ r.post.atoms, r.post.SameComponent v w :=
  r.post_connected_of_two_boundary_labels 3 3 (by decide) (by decide) (Relation.EqvGen.refl _) hconn

/-- In scenario 6 the side of vertex 4 would have just its single bond 24
on the old boundary if it were separated from vertex 3. -/
theorem appb_s33new6_boundary_connected (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new6.pattern)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    r.post.SameComponent (r.vertex 3) (r.vertex 4) := by
  classical
  by_contra hn
  let S := Degen.residualComponent M r.removedAtoms (r.vertex 4)
  have h4M := r.vertex_mem 4 (by decide)
  have h4Y : r.vertex 4 ∉ r.removedAtoms :=
    fun h => (show 4 ∉ AppbPatternKind.s33new6.pattern.removed by decide)
      ((r.vertex_mem_removed_iff 4 (by decide)).mp h)
  have h4S : r.vertex 4 ∈ S := (Degen.mem_residualComponent M r.removedAtoms (r.vertex 4) _).mpr
    ⟨h4M,h4Y,Relation.EqvGen.refl _⟩
  have h3S : r.vertex 3 ∉ S := by
    intro h
    have hh := (Degen.mem_residualComponent M r.removedAtoms (r.vertex 4) _).mp h
    exact hn ((Degen.eraseAtoms_sameComponent_iff M r.removedAtoms _ _).mpr hh.2.2).symm
  have hnotS (a : ℕ) (ha : a ∈ AppbPatternKind.s33new6.pattern.removed) : r.vertex a ∉ S := by
    intro h
    exact ((Degen.mem_residualComponent M r.removedAtoms (r.vertex 4) _).mp h).2.1 (mem_image_of_mem _ ha)
  apply r.cutCount_ne_one S (r.residual_cut_crossing (r.vertex 4)) hbridge
  change (∑ i : Fin 5, if
    (r.vertex ([(1,2),(1,3),(1,3),(2,3),(2,4)][i].1) ∈ S ∧
      r.vertex ([(1,2),(1,3),(1,3),(2,3),(2,4)][i].2) ∉ S) ∨
    (r.vertex ([(1,2),(1,3),(1,3),(2,3),(2,4)][i].1) ∉ S ∧
      r.vertex ([(1,2),(1,3),(1,3),(2,3),(2,4)][i].2) ∈ S) then 1 else 0) = 1
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num [hnotS 1 (by decide),hnotS 2 (by decide),h3S,h4S]

/-- Full ambient post connectivity in scenario 6. -/
theorem appb_s33new6_post_connected (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33new6.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    ∀ v ∈ r.post.atoms, ∀ w ∈ r.post.atoms, r.post.SameComponent v w :=
  r.post_connected_of_two_boundary_labels 3 4 (by decide) (by decide)
    (appb_s33new6_boundary_connected M r hbridge) hconn

end WaveTurbulence.Mole
