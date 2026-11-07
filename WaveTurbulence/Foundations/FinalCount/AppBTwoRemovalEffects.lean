/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleBondEffects
public import WaveTurbulence.Foundations.FinalCount.AppBSmallCutEffects
import Mathlib.Tactic

/-! # DH23 2rprop: circuit and nu effects in all degree-two removals -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- All three open degree-two removal patterns retain one component. -/
theorem appb_r2_open_graph_effect (M : Molecule V D) (k : AppbPatternKind)
    (hk : k ∈ ([AppbPatternKind.r21,.r22,.r23] : List _))
    (r : AppbRealization M k.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    r.post.numComponents = M.numComponents ∧
    r.post.circuitRank - M.circuitRank = -1 ∧
    appbNu r.post - appbNu M = (if k = .r23 then -4 else 0) := by
  have hp : k.pattern.removed.Nonempty ∧ 0 < k.pattern.boundaryCount ∧ k.pattern.boundaryCount ≤ 3 := by
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    have he := List.mem_singleton.mp hk
    subst k
    decide
  obtain ⟨hf,hchi,hnu⟩ := r.small_boundary_graph_effects hconn hbridge hp.1 hp.2.1 hp.2.2
  refine ⟨hf,?_,?_⟩
  · rw [hchi]
    rcases List.mem_cons.mp hk with rfl | hk
    · norm_num [AppbPatternKind.pattern]
    rcases List.mem_cons.mp hk with rfl | hk
    · norm_num [AppbPatternKind.pattern]
    have he := List.mem_singleton.mp hk
    subst k
    norm_num [AppbPatternKind.pattern]
  · rw [hnu]
    rcases List.mem_cons.mp hk with rfl | hk
    · norm_num [AppbPatternKind.pattern]
    rcases List.mem_cons.mp hk with rfl | hk
    · norm_num [AppbPatternKind.pattern]
    have he := List.mem_singleton.mp hk
    subst k
    norm_num [AppbPatternKind.pattern]

/-- 2R-3F also permits the two external neighbours to coincide. This case
retains that actual common atom and has the same -1 circuit effect. -/
theorem appb_r23_common_graph_effect (M : Molecule V D)
    (r : AppbRealization M appbR23Common)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    r.post.numComponents = M.numComponents ∧
    r.post.circuitRank - M.circuitRank = -1 ∧ appbNu r.post - appbNu M = -4 := by
  simpa [appbR23Common] using r.small_boundary_graph_effects hconn hbridge (by decide) (by decide) (by decide)

/-- The triangle and isolated double component disappear entirely. -/
theorem appb_r2_closed_graph_effect (M : Molecule V D) (k : AppbPatternKind)
    (hk : k ∈ ([AppbPatternKind.r23triangle,.r24] : List _))
    (r : AppbRealization M k.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) :
    r.post.numComponents = 0 ∧ M.numComponents = 1 ∧
    r.post.circuitRank - M.circuitRank = -1 ∧
    appbNu r.post - appbNu M = (if k = .r23triangle then -2 else 0) := by
  have hp : k.pattern.removed.Nonempty ∧ k.pattern.boundaryCount = 0 := by
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    have he := List.mem_singleton.mp hk
    subst k
    decide
  have hz := r.post_atoms_empty_of_boundary_zero hconn hp.1 hp.2
  have hf : r.post.numComponents = 0 := by
    have hh := numComponents_le_card_atoms r.post
    rw [hz,card_empty] at hh
    omega
  have hm : M.numComponents = 1 := numComponents_eq_one M (by
    obtain ⟨a,ha⟩ := hp.1
    exact ⟨r.vertex a,r.vertex_mem a (mem_union_left _ ha)⟩) hconn
  refine ⟨hf,hm,?_,?_⟩
  · rw [r.post_circuitRank,hf,hm]
    rcases List.mem_cons.mp hk with rfl | hk
    · norm_num [AppbPatternKind.pattern]
    have he := List.mem_singleton.mp hk
    subst k
    norm_num [AppbPatternKind.pattern]
  · rw [r.post_nu,hf,hm]
    rcases List.mem_cons.mp hk with rfl | hk
    · norm_num [AppbPatternKind.pattern]
    have he := List.mem_singleton.mp hk
    subst k
    norm_num [AppbPatternKind.pattern]

end WaveTurbulence.Mole
