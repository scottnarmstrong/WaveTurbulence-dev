/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBSharedDoubleTopology
public import WaveTurbulence.Foundations.FinalCount.AppBComponentEffects
public import WaveTurbulence.Foundations.FinalCount.AppBReturningTriangleTopology
public import WaveTurbulence.Foundations.FinalCount.AppBMixedDoubleTopology
import Mathlib.Tactic

/-! # DH23 3s3prop: all literal-deletion component and circuit effects -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every single-pair configuration either retains its component or splits
it into two. The two exact chi/nu effects are computed, not assumed. -/
theorem appb_s33_remove_graph_effect (M : Molecule V D) (k : AppbPatternKind)
    (hk : k ∈ ([AppbPatternKind.s33,.s33new1,.s33new2,.s33new3,.s33new4,.s33new5,.s33new6] : List _))
    (r : AppbRealization M k.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    (r.post.numComponents = M.numComponents ∧ r.post.circuitRank - M.circuitRank = -3 ∧
      appbNu r.post - appbNu M = 2) ∨
    (r.post.numComponents = M.numComponents + 1 ∧ r.post.circuitRank - M.circuitRank = -2 ∧
      appbNu r.post - appbNu M = -2) := by
  have ht : ∀ k ∈ ([AppbPatternKind.s33,.s33new1,.s33new2,.s33new3,.s33new4,.s33new5,.s33new6] : List _),
      k.pattern.edges.length = 5 ∧ k.pattern.removed.card = 2 ∧ k.pattern.boundaryCount = 4 ∧
      k.pattern.removed.Nonempty ∧ 1 ∈ k.pattern.vertices := by decide
  obtain ⟨he,hv,hb,hne,h1⟩ := ht k hk
  have hbound := r.two_mul_post_components_le hconn hbridge hne
  have hpos := appb_numComponents_pos r.post (r.post_atoms_nonempty (by omega))
  have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 h1⟩ hconn
  have hf : r.post.numComponents = 1 ∨ r.post.numComponents = 2 := by omega
  rcases hf with hf | hf
  · left
    refine ⟨hf.trans hm.symm,?_,?_⟩
    · rw [r.post_circuitRank,hf,hm,he,hv]; norm_num
    · rw [r.post_nu,hf,hm,he,hv]; norm_num
  · right
    refine ⟨by omega,?_,?_⟩
    · rw [r.post_circuitRank,hf,hm,he,hv]; norm_num
    · rw [r.post_nu,hf,hm,he,hv]; norm_num

/-- Scenarios 3–6 actually retain one component; the alternative split
would expose an old bridge, as proved from the transcribed local cuts. -/
theorem appb_s33new_double_graph_effect (M : Molecule V D) (k : AppbPatternKind)
    (hk : k ∈ ([AppbPatternKind.s33new3,.s33new4,.s33new5,.s33new6] : List _))
    (r : AppbRealization M k.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    r.post.numComponents = M.numComponents ∧
    r.post.circuitRank - M.circuitRank = -3 ∧ appbNu r.post - appbNu M = 2 := by
  have hpost : ∀ v ∈ r.post.atoms, ∀ w ∈ r.post.atoms, r.post.SameComponent v w := by
    rcases List.mem_cons.mp hk with rfl | hk
    · exact appb_s33new3_post_connected M r hconn hbridge
    rcases List.mem_cons.mp hk with rfl | hk
    · exact appb_s33new4_post_connected M r hconn
    rcases List.mem_cons.mp hk with rfl | hk
    · exact appb_s33new5_post_connected M r hconn hbridge
    have he := List.mem_singleton.mp hk
    subst k
    exact appb_s33new6_post_connected M r hconn hbridge
  have ht : ∀ k ∈ ([AppbPatternKind.s33new3,.s33new4,.s33new5,.s33new6] : List _),
      k.pattern.edges.length = 5 ∧ k.pattern.removed.card = 2 ∧ k.pattern.boundaryCount = 4 ∧
      1 ∈ k.pattern.vertices := by decide
  obtain ⟨he,hv,hb,h1⟩ := ht k hk
  have hf := numComponents_eq_one r.post (r.post_atoms_nonempty (by omega)) hpost
  have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 h1⟩ hconn
  refine ⟨hf.trans hm.symm,?_,?_⟩
  · rw [r.post_circuitRank,hf,hm,he,hv]; norm_num
  · rw [r.post_nu,hf,hm,he,hv]; norm_num

end WaveTurbulence.Mole
