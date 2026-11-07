/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ConnectedDeletionComponents
public import WaveTurbulence.Foundations.FinalCount.Algorithm.RealizedAdjacency
public import WaveTurbulence.Foundations.FinalCount.Algorithm.GlobalSmallBoundaryEffects
public import WaveTurbulence.Foundations.FinalCount.AppBNormalDegreeEffects
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
import Mathlib.Tactic

/-! # Normal S33 statistics with unrelated components present -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem s33_global_components_split (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e)
    (hsep : ¬r.post.SameComponent (r.vertex 3) (r.vertex 4)) :
    r.post.numComponents = M.numComponents+1 := by
  classical
  have h1 : r.vertex 1 ∈ r.removedAtoms := mem_image_of_mem _ (by decide)
  have h3 := new_component_mem_of_adj_removed M r.removedAtoms h1
    (r.vertex_mem_post 3 (by decide) (by decide)) (realized_edge_adj r (1 : Fin 5))
  have h4 := new_component_mem_of_adj_removed M r.removedAtoms h1
    (r.vertex_mem_post 4 (by decide) (by decide)) (realized_edge_adj r (2 : Fin 5))
  have hne : Degen.residualComponent M r.removedAtoms (r.vertex 3) ≠
      Degen.residualComponent M r.removedAtoms (r.vertex 4) := by
    intro he
    have h4mem : r.vertex 4 ∈ Degen.residualComponent M r.removedAtoms (r.vertex 4) :=
      (Degen.mem_residualComponent M r.removedAtoms _ _).mpr
        ⟨r.vertex_mem 4 (by decide),(mem_sdiff.mp (r.vertex_mem_post 4 (by decide) (by decide))).2,
          Relation.EqvGen.refl _⟩
    rw [← he] at h4mem
    exact hsep ((Degen.eraseAtoms_sameComponent_iff M r.removedAtoms _ _).mpr
      ((Degen.mem_residualComponent M r.removedAtoms _ _).mp h4mem).2.2)
  have hlo : 1 < (Degen.newComponents M r.removedAtoms).card := one_lt_card.mpr ⟨_,h3,_,h4,hne⟩
  have hhi := Degen.two_mul_card_newComponents_le M hbridge r.removedAtoms
  have hb : AppbPatternKind.s33.pattern.boundaryCount = 4 := by decide
  rw [r.boundary_card,hb] at hhi
  have hnew : (Degen.newComponents M r.removedAtoms).card = 2 := by omega
  have hconn := FigurePaths.removed_connected_of_center_incidence r
    (patterns_removed_center_incidence .s33 (by decide))
  have hf : r.post.numComponents+1 = M.numComponents+(Degen.newComponents M r.removedAtoms).card :=
    numComponents_erase_connected_add_one M r.removedAtoms h1 (r.vertex_mem 1 (by decide))
      (fun y hy => hconn y hy _ h1)
  rw [hnew] at hf
  omega

theorem s33_normal_global_statistics (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern)
    (hbridge : ∀ e : D,¬Degen.IsBridge M e)
    (hsep : ¬r.post.SameComponent (r.vertex 3) (r.vertex 4))
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4)
    (h5 : M.deg (r.vertex 5) = 4) (h6 : M.deg (r.vertex 6) = 4) :
    appbNu r.post-appbNu M = -2 ∧
      ((appbDegreeAtoms r.post 3).card : ℤ)-(appbDegreeAtoms M 3).card = 2 := by
  have hf := s33_global_components_split M r hbridge hsep
  have hfz : (r.post.numComponents : ℤ) = M.numComponents+1 := by exact_mod_cast hf
  refine ⟨?_,appb_s33_normal_degreeThree M r h3 h4 h5 h6⟩
  rw [r.post_nu,hfz]
  norm_num [show AppbPatternKind.s33.pattern.removed.card = 2 by decide,
    show AppbPatternKind.s33.pattern.edges.length = 5 by decide]

end WaveTurbulence.Mole.AppbAlgorithm
