/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertionGraphEffects
public import WaveTurbulence.Foundations.FinalCount.AppBBranchConditions
public import WaveTurbulence.Foundations.FinalCount.AppBSmallCutEffects
import Mathlib.Tactic

/-! # DH23 3S3-3G and 3D3-3G: exact combined graph effects -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Equality of the actual component quotient with one element implies
connectivity of every two actual atoms. -/
theorem appb_connected_of_numComponents_eq_one (M : Molecule V D) (h : M.numComponents = 1)
    {u v : V} (hu : u ∈ M.atoms) (hv : v ∈ M.atoms) : M.SameComponent u v := by
  have hs : Subsingleton (AppbComponents M) := (Nat.card_eq_one_iff_unique.mp h).1
  exact (quotient_eq_iff_sameComponent M ⟨u,hu⟩ ⟨v,hv⟩).mp (hs.elim _ _)

/-- 3S3-3G keeps the two residual components and loses only one circuit
after the actual oriented bond 35 is reinserted. -/
theorem appb_s33_good_reinsert_graph_effect (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hgeom : AppbS33SplitGeometry M r) :
    (r.directedPostWithBond 3 5 ⟨1,by decide⟩).numComponents = M.numComponents + 1 ∧
    (r.directedPostWithBond 3 5 ⟨1,by decide⟩).circuitRank - M.circuitRank = -1 ∧
    appbNu (r.directedPostWithBond 3 5 ⟨1,by decide⟩) - appbNu M = -4 := by
  have hf := appb_numComponents_eq_two r.post hgeom.1
  have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hconn
  obtain ⟨hnewF,hnewChi,hnewNu⟩ := r.directedPostWithBond_graph_effects 3 5 ⟨1,by decide⟩
    (by decide) (by decide) (by decide) (by decide) hgeom.2.1
  have hchi : r.post.circuitRank - M.circuitRank = -2 := by
    rw [r.post_circuitRank,hf,hm]
    norm_num [AppbPatternKind.pattern]
  have hnu : appbNu r.post - appbNu M = -2 := by
    rw [r.post_nu,hf,hm]
    norm_num [AppbPatternKind.pattern]
  refine ⟨by omega,?_,?_⟩
  · omega
  · omega

/-- 3D3-3G retains the component and loses only one circuit after the
actual oriented bond 34 is reinserted. -/
theorem appb_d33_good_reinsert_graph_effect (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    (r.directedPostWithBond 3 4 ⟨2,by decide⟩).numComponents = M.numComponents ∧
    (r.directedPostWithBond 3 4 ⟨2,by decide⟩).circuitRank - M.circuitRank = -1 ∧
    appbNu (r.directedPostWithBond 3 4 ⟨2,by decide⟩) - appbNu M = -2 := by
  have hf := r.post_numComponents_eq_one_of_small_boundary hconn hbridge (by decide) (by decide) (by decide)
  have hpath := appb_connected_of_numComponents_eq_one r.post hf
    (r.vertex_mem_post 3 (by decide) (by decide)) (r.vertex_mem_post 4 (by decide) (by decide))
  obtain ⟨hnewF,hnewChi,hnewNu⟩ := r.directedPostWithBond_graph_effects 3 4 ⟨2,by decide⟩
    (by decide) (by decide) (by decide) (by decide) hpath
  obtain ⟨hOldF,hchi,hnu⟩ := appb_d33_graph_effect M r hconn hbridge
  refine ⟨hnewF.trans hOldF,?_,?_⟩
  · omega
  · omega

end WaveTurbulence.Mole
