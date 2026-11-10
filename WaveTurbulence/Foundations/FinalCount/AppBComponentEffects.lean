/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBoundaryCounts
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeComponents
import Mathlib.Tactic

/-! # Appendix B component and circuit effects from actual cuts -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- An actual surviving atom witnesses a component, even if isolated. -/
theorem appb_numComponents_pos (M : Molecule V D) (hv : M.atoms.Nonempty) :
    0 < M.numComponents := by
  obtain ⟨v,hv⟩ := hv
  have : Nonempty (AppbComponents M) := ⟨appbComponent M ⟨v,hv⟩⟩
  exact Nat.card_pos

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- A nonempty figure boundary supplies an actual surviving atom. -/
theorem post_atoms_nonempty (hb : 0 < P.boundaryCount) : r.post.atoms.Nonempty := by
  have hc : 0 < (Degen.boundaryDarts M r.removedAtoms).card := by rw [r.boundary_card]; exact hb
  obtain ⟨x,hx⟩ := card_pos.mp hc
  have hx' := (mem_filter.mp hx).2
  exact ⟨M.atom (M.mate x), mem_sdiff.mpr ⟨M.atom_mem _,hx'.2⟩⟩

/-- In a bridgeless connected molecule a cut with two or three boundary
bonds leaves exactly one component. This computes its actual quotient. -/
theorem post_numComponents_eq_one_of_small_boundary
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) (hne : P.removed.Nonempty)
    (hb : 0 < P.boundaryCount) (hsmall : P.boundaryCount ≤ 3) : r.post.numComponents = 1 := by
  have hle := r.two_mul_post_components_le hconn hbridge hne
  have hpos := appb_numComponents_pos r.post (r.post_atoms_nonempty hb)
  omega

end AppbRealization

/-- DH23 3D4: the exact circuit-rank change is -3, derived from the figure
and no-bridge premise, rather than assumed as operation data. -/
theorem appb_d34_circuit_effect (k : AppbPatternKind)
    (hk : k ∈ ([AppbPatternKind.d34one, .d34two, .d34three, .d34four] : List _))
    (M : Molecule V D) (r : AppbRealization M k.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    r.post.circuitRank - M.circuitRank = -3 ∧ appbNu r.post - appbNu M = 2 := by
  have hb : k.pattern.removed.Nonempty ∧ 0 < k.pattern.boundaryCount ∧ k.pattern.boundaryCount ≤ 3 := by
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    have he := List.mem_singleton.mp hk
    subst k
    decide
  have hf := r.post_numComponents_eq_one_of_small_boundary hconn hbridge hb.1 hb.2.1 hb.2.2
  have hm := numComponents_eq_one M (by
    obtain ⟨a,ha⟩ := hb.1
    exact ⟨r.vertex a,r.vertex_mem a (mem_union_left _ ha)⟩) hconn
  have hs : k.pattern.edges.length = 5 ∧ k.pattern.removed.card = 2 := by
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    rcases List.mem_cons.mp hk with rfl | hk
    · decide
    have he := List.mem_singleton.mp hk
    subst k
    decide
  constructor
  · rw [r.post_circuitRank,hf,hm,hs.1,hs.2]
    norm_num
  · rw [r.post_nu,hf,hm,hs.1,hs.2]
    norm_num

end WaveTurbulence.Mole
