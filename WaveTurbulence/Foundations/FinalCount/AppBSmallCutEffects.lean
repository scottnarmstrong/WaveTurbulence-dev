/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBComponentEffects
import Mathlib.Tactic

/-! # Exact Appendix B effects for cuts of at most three boundary bonds -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- General local cut calculation. All component information follows from
connectedness and absence of bridges, and finite pattern facts. -/
theorem small_boundary_graph_effects
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) (hne : P.removed.Nonempty)
    (hb : 0 < P.boundaryCount) (hsmall : P.boundaryCount ≤ 3) :
    r.post.numComponents = M.numComponents ∧
    r.post.circuitRank - M.circuitRank = -(P.edges.length : ℤ) + P.removed.card ∧
    appbNu r.post - appbNu M = -4 * (P.removed.card : ℤ) + 2 * P.edges.length := by
  have hf := r.post_numComponents_eq_one_of_small_boundary hconn hbridge hne hb hsmall
  have hm := numComponents_eq_one M (by
    obtain ⟨a,ha⟩ := hne
    exact ⟨r.vertex a,r.vertex_mem a (mem_union_left _ ha)⟩) hconn
  refine ⟨hf.trans hm.symm,?_,?_⟩
  · rw [r.post_circuitRank,hf,hm]
    ring
  · rw [r.post_nu,hf,hm]
    ring

end AppbRealization

/-- DH23 3d3prop: the double-pair deletion has chi change -2 and nu change
zero. The extra normal-case boundary degree conditions affect V3 only. -/
theorem appb_d33_graph_effect (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    r.post.numComponents = M.numComponents ∧
    r.post.circuitRank - M.circuitRank = -2 ∧ appbNu r.post - appbNu M = 0 := by
  simpa [show AppbPatternKind.d33.pattern.edges.length = 4 by decide,
    show AppbPatternKind.d33.pattern.removed.card = 2 by decide] using
    r.small_boundary_graph_effects hconn hbridge (by decide) (by decide) (by decide)

/-- DH23 3rprop: removing the degree-three star has chi change -2 and
nu change +2. -/
theorem appb_r3_graph_effect (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.r3.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    r.post.numComponents = M.numComponents ∧
    r.post.circuitRank - M.circuitRank = -2 ∧ appbNu r.post - appbNu M = 2 := by
  simpa [show AppbPatternKind.r3.pattern.edges.length = 3 by decide,
    show AppbPatternKind.r3.pattern.removed.card = 1 by decide] using
    r.small_boundary_graph_effects hconn hbridge (by decide) (by decide) (by decide)

/-- DH23 3s2prop: each of the four local configurations has chi change -2
and nu change zero. -/
theorem appb_s32_graph_effect (M : Molecule V D) (k : AppbPatternKind)
    (hk : k ∈ ([AppbPatternKind.s32one,.s32two,.s32three,.s32four] : List _))
    (r : AppbRealization M k.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    r.post.numComponents = M.numComponents ∧
    r.post.circuitRank - M.circuitRank = -2 ∧ appbNu r.post - appbNu M = 0 := by
  have hp : k.pattern.removed.Nonempty ∧ 0 < k.pattern.boundaryCount ∧
      k.pattern.boundaryCount ≤ 3 ∧ k.pattern.edges.length = 4 ∧ k.pattern.removed.card = 2 := by
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    have he := List.mem_singleton.mp hk
    subst k
    decide
  simpa [hp.2.2.2.1,hp.2.2.2.2] using
    r.small_boundary_graph_effects hconn hbridge hp.1 hp.2.1 hp.2.2.1

end WaveTurbulence.Mole
