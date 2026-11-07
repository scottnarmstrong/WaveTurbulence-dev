/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBComponentEffects
import Mathlib.Tactic

/-! # DH23 triple-bond operation graph effects -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- A boundary-free nonempty deleted set exhausts its connected component. -/
theorem post_atoms_empty_of_boundary_zero
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hne : P.removed.Nonempty) (hb : P.boundaryCount = 0) : r.post.atoms = ∅ := by
  have hzero : Degen.boundaryDarts M r.removedAtoms = ∅ := by
    apply card_eq_zero.mp
    rw [r.boundary_card,hb]
  obtain ⟨a,ha⟩ := hne
  have haY : r.vertex a ∈ r.removedAtoms := mem_image_of_mem _ ha
  have haM : r.vertex a ∈ M.atoms := r.removedAtoms_subset haY
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvM,hvY⟩ := mem_sdiff.mp hv
  have hp := hconn (r.vertex a) haM v hvM
  exact hvY ((Degen.sameComponent_mem_iff_of_boundary_empty M _ hzero hp).mp haY)

/-- A one-bond boundary leaves exactly one component, with no assumption
that the original graph is bridgeless. -/
theorem post_numComponents_eq_one_of_boundary_one
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hne : P.removed.Nonempty) (hb : P.boundaryCount = 1) : r.post.numComponents = 1 := by
  have hY : r.removedAtoms.Nonempty := hne.image r.vertex
  have hcard : (Degen.newComponents M r.removedAtoms).card ≤
      (Degen.boundaryDarts M r.removedAtoms).card := by
    calc
      _ = ∑ _S ∈ Degen.newComponents M r.removedAtoms, 1 := by simp
      _ ≤ ∑ S ∈ Degen.newComponents M r.removedAtoms, (Degen.boundaryDarts M S).card := by
        apply sum_le_sum
        intro S hS
        exact card_pos.mpr (mem_filter.mp hS).2
      _ ≤ _ := Degen.sum_newComponents_boundary_card_le M r.removedAtoms
  rw [r.boundary_card,hb] at hcard
  have he := Degen.numComponents_eraseAtoms_eq_card_newComponents M hconn _ hY r.removedAtoms_subset
  have hp := appb_numComponents_pos r.post (r.post_atoms_nonempty (by omega))
  change r.post.numComponents = _ at he
  omega

end AppbRealization

/-- DH23 TB-1N: the isolated triple pair disappears. -/
theorem appb_tb1_graph_effect (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.tb1.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) :
    r.post.numComponents = 0 ∧ M.numComponents = 1 ∧
    r.post.circuitRank - M.circuitRank = -2 ∧ appbNu r.post - appbNu M = 2 := by
  have hzero := r.post_atoms_empty_of_boundary_zero hconn (by decide) (by decide)
  have hf : r.post.numComponents = 0 := by
    have hh := numComponents_le_card_atoms r.post
    rw [hzero,card_empty] at hh
    omega
  have hm : M.numComponents = 1 := numComponents_eq_one M
    ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hconn
  refine ⟨hf,hm,?_,?_⟩
  · rw [r.post_circuitRank,hf,hm]
    norm_num [AppbPatternKind.pattern]
  · rw [r.post_nu,hf,hm]
    norm_num [AppbPatternKind.pattern]

/-- DH23 TB-2N: the external single bond leaves a connected residual graph. -/
theorem appb_tb2_graph_effect (M : Molecule V D)
    (r : AppbRealization M AppbPatternKind.tb2.pattern)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) :
    r.post.numComponents = M.numComponents ∧
    r.post.circuitRank - M.circuitRank = -2 ∧ appbNu r.post - appbNu M = 0 := by
  have hf := r.post_numComponents_eq_one_of_boundary_one hconn (by decide) (by decide)
  have hm : M.numComponents = 1 := numComponents_eq_one M
    ⟨r.vertex 1,r.vertex_mem 1 (by decide)⟩ hconn
  refine ⟨hf.trans hm.symm,?_,?_⟩
  · rw [r.post_circuitRank,hf,hm]
    norm_num [AppbPatternKind.pattern]
  · rw [r.post_nu,hf,hm]
    norm_num [AppbPatternKind.pattern]

end WaveTurbulence.Mole
