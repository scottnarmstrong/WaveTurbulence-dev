/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPostComponentBound
import Mathlib.Tactic

/-! # DH23 3D3-6G: exact four-atom nine-bond removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The two Figure 3D3New alternatives, calculated on the actual quotient. -/
theorem appb_d336_graph_effect (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.d33new.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    (r.post.numComponents = M.numComponents ∧ r.post.circuitRank - M.circuitRank = -5 ∧
      appbNu r.post - appbNu M = 2) ∨
    (r.post.numComponents = M.numComponents + 1 ∧ r.post.circuitRank - M.circuitRank = -4 ∧
      appbNu r.post - appbNu M = -2) := by
  have hbound := r.two_mul_post_components_le hconn hbridge (by decide)
  have hb : AppbPatternKind.d33new.pattern.boundaryCount = 4 := by decide
  rw [hb] at hbound
  have hpos := appb_numComponents_pos r.post (r.post_atoms_nonempty (by decide))
  have hf : r.post.numComponents = 1 ∨ r.post.numComponents = 2 := by omega
  have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hconn
  rcases hf with hf | hf
  · left
    refine ⟨hf.trans hm.symm,?_,?_⟩
    · rw [r.post_circuitRank,hf,hm]
      norm_num [AppbPatternKind.pattern]
    · rw [r.post_nu,hf,hm]
      norm_num [AppbPatternKind.pattern]
  · right
    refine ⟨by omega,?_,?_⟩
    · rw [r.post_circuitRank,hf,hm]
      norm_num [AppbPatternKind.pattern]
    · rw [r.post_nu,hf,hm]
      norm_num [AppbPatternKind.pattern]

end WaveTurbulence.Mole
