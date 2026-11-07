/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPostComponentBound
public import WaveTurbulence.Foundations.FinalCount.AppBSmallCutEffects
public import WaveTurbulence.Foundations.FinalCount.AppBGoodReinsertionEffects
import Mathlib.Tactic

/-! # DH23 3R-2G: sequential star and residual special-pair removal

Using two actual realizations automatically handles overlaps between the
three original neighbours and the four residual special-pair vertices.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The actual two-step deletion removes exactly three vertices and eight
bonds, regardless of allowed overlaps in Figure 3RProof. -/
theorem appb_r32_counts (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern) :
    s.post.atoms.card + 3 = M.atoms.card ∧ s.post.bonds.card + 8 = M.bonds.card := by
  have hv1 := r.post_card_atoms
  have hv2 := s.post_card_atoms
  have he1 := r.post_card_bonds
  have he2 := s.post_card_bonds
  norm_num [AppbPatternKind.pattern] at hv1 hv2 he1 he2
  omega

/-- Exact 3R-2G graph alternatives. The -4 or -5 circuit change is derived
from the actual residual quotient and the sequential eight-bond count. -/
theorem appb_r32_graph_effect (M : Molecule V D) (r : AppbRealization M AppbPatternKind.r3.pattern)
    (s : AppbRealization r.post AppbPatternKind.s33new3.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hbridge : ∀ e : D, ¬ Degen.IsBridge M e) :
    (s.post.numComponents = M.numComponents ∧ s.post.circuitRank - M.circuitRank = -5 ∧
      appbNu s.post - appbNu M = 4) ∨
    (s.post.numComponents = M.numComponents + 1 ∧ s.post.circuitRank - M.circuitRank = -4 ∧
      appbNu s.post - appbNu M = 0) := by
  have hf0 := r.post_numComponents_eq_one_of_small_boundary hconn hbridge (by decide) (by decide) (by decide)
  have hconn0 : ∀ u ∈ r.post.atoms, ∀ v ∈ r.post.atoms, r.post.SameComponent u v := by
    intro u hu v hv
    exact appb_connected_of_numComponents_eq_one r.post hf0 hu hv
  have hm := numComponents_eq_one M ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hconn
  have hf := s.special_pair_post_components hconn0
  obtain ⟨hv,he⟩ := appb_r32_counts M r s
  have hvz : (s.post.atoms.card : ℤ) + 3 = M.atoms.card := by exact_mod_cast hv
  have hez : (s.post.bonds.card : ℤ) + 8 = M.bonds.card := by exact_mod_cast he
  rcases hf with hf | hf
  · left
    refine ⟨hf.trans hm.symm,?_,?_⟩
    · unfold Molecule.circuitRank
      rw [hf,hm]
      omega
    · unfold appbNu
      rw [hf,hm]
      omega
  · right
    refine ⟨by omega,?_,?_⟩
    · unfold Molecule.circuitRank
      rw [hf,hm]
      omega
    · unfold appbNu
      rw [hf,hm]
      omega

end WaveTurbulence.Mole
