/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBNormalDegreeEffects
public import WaveTurbulence.Foundations.FinalCount.AppBSmallCutEffects
public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponents
import Mathlib.Tactic

/-! # DH23 Appendix B: normal-operation graph effects

The 3S3 residual two-component topology is exactly the source condition
(i), stated as actual connected pieces rather than an assumed count.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- DH23 3s3prop normal-case graph identities. -/
theorem appb_s33_normal_graph_effect (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.s33.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (htwo : TwoComponents r.post r.post.atoms (r.vertex 3) (r.vertex 4))
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4)
    (h5 : M.deg (r.vertex 5) = 4) (h6 : M.deg (r.vertex 6) = 4) :
    r.post.numComponents = M.numComponents + 1 ∧
    r.post.circuitRank - M.circuitRank = -2 ∧
    appbNu r.post - appbNu M = -2 ∧
    ((appbDegreeAtoms r.post 3).card : ℤ) - (appbDegreeAtoms M 3).card = 2 := by
  have hf := appb_numComponents_eq_two r.post htwo
  have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hconn
  refine ⟨?_,?_,?_,appb_s33_normal_degreeThree M r h3 h4 h5 h6⟩
  · omega
  · rw [r.post_circuitRank,hf,hm]
    norm_num [AppbPatternKind.pattern]
  · rw [r.post_nu,hf,hm]
    norm_num [AppbPatternKind.pattern]

/-- DH23 3d3prop normal-case graph identities. -/
theorem appb_d33_normal_graph_effect (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e)
    (h3 : M.deg (r.vertex 3) = 4) (h4 : M.deg (r.vertex 4) = 4) :
    r.post.numComponents = M.numComponents ∧
    r.post.circuitRank - M.circuitRank = -2 ∧
    appbNu r.post - appbNu M = 0 ∧
    ((appbDegreeAtoms r.post 3).card : ℤ) - (appbDegreeAtoms M 3).card = 0 := by
  obtain ⟨hf,hchi,hnu⟩ := appb_d33_graph_effect M r hconn hbridge
  exact ⟨hf,hchi,hnu,appb_d33_normal_degreeThree M r h3 h4⟩

/-- DH23 3rprop normal-case graph identities. -/
theorem appb_r3_normal_graph_effect (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e)
    (h2 : M.deg (r.vertex 2) = 4) (h3 : M.deg (r.vertex 3) = 4)
    (h4 : M.deg (r.vertex 4) = 4) :
    r.post.numComponents = M.numComponents ∧
    r.post.circuitRank - M.circuitRank = -2 ∧
    appbNu r.post - appbNu M = 2 ∧
    ((appbDegreeAtoms r.post 3).card : ℤ) - (appbDegreeAtoms M 3).card = 2 := by
  obtain ⟨hf,hchi,hnu⟩ := appb_r3_graph_effect M r hconn hbridge
  exact ⟨hf,hchi,hnu,appb_r3_normal_degreeThree M r h2 h3 h4⟩

end WaveTurbulence.Mole
