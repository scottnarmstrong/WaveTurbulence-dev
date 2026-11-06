/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.MoleculeOneJointCrossing
public import WaveTurbulence.Foundations.Spine.MoleculeCommonJointDegree
public import WaveTurbulence.Foundations.Spine.MoleculeOverlapDeletion
import Mathlib.Tactic

/-!
# DH23 Lemma 4.11(b): exactly one common joint

An additional common atom would force both remaining joints into the
opposite interiors. The common joint then has only its two shared
incidences; deleting the crossed interior joint contradicts the source
two-component condition. Thus only the common joint is shared.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- With one common joint, the source interior/deletion premises exclude
all further shared atoms, for both block and hyper-block realizations. -/
theorem realized_one_joint_intersection (hM : M.IsMolecule) {A B : Finset V} {a b c : V}
    (RA : BlockRealization M A a c) (RB : BlockRealization M B b c) (hab : a ≠ b)
    (hnotA : ¬ A ⊆ B) (hnotB : ¬ B ⊆ A)
    (hintA : ∀ u ∈ A \ {a,c}, ∀ v ∈ A \ {a,c}, (induced M (A \ {a,c})).SameComponent u v)
    (hintB : ∀ u ∈ B \ {b,c}, ∀ v ∈ B \ {b,c}, (induced M (B \ {b,c})).SameComponent u v)
    (hdelA : InteriorDeletionProperty M A a c) : A ∩ B = {c} := by
  apply Finset.Subset.antisymm
  · intro x hx
    apply Finset.mem_singleton.mpr
    by_contra hxc
    have hextra : ∃ u ∈ A ∩ B, u ≠ c := ⟨x,hx,hxc⟩
    have hbA := one_joint_extra_forces_crossing M hM RA RB hab hnotA hextra hintA
    have hextra' : ∃ u ∈ B ∩ A, u ≠ c := by rw [Finset.inter_comm]; exact hextra
    have haB := one_joint_extra_forces_crossing M hM RB RA (Ne.symm hab) hnotB hextra' hintB
    have hnoC := common_crossed_no_exterior_edge M hM RA RB hab haB hbA
    have hcA := RA.joints_mem_ne.2.1
    have hcB := RB.joints_mem_ne.2.1
    have hbB := RB.joints_mem_ne.1
    have hbc := RB.joints_mem_ne.2.2
    have hcover : (A \ B) ∪ (A ∩ B).erase b = A.erase b := by
      ext z
      by_cases hz : z = b
      · subst z
        simp [hbB]
      · simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,Finset.mem_erase]
        tauto
    have hdis : Disjoint (A \ B) ((A ∩ B).erase b) := by
      apply Finset.disjoint_left.mpr
      intro z hzP hzQ
      exact (Finset.mem_sdiff.mp hzP).2 (Finset.mem_inter.mp (Finset.mem_erase.mp hzQ).2).2
    have hP : (A \ B).Nonempty := by
      obtain ⟨z,hzA,hzB⟩ := Finset.not_subset.mp hnotA
      exact ⟨z,Finset.mem_sdiff.mpr ⟨hzA,hzB⟩⟩
    have hcQ : c ∈ (A ∩ B).erase b :=
      Finset.mem_erase.mpr ⟨Ne.symm hbc,Finset.mem_inter.mpr ⟨hcA,hcB⟩⟩
    have haQ : a ∈ (A ∩ B).erase b :=
      Finset.mem_erase.mpr ⟨hab,Finset.mem_inter.mpr ⟨RA.joints_mem_ne.1,haB⟩⟩
    have hQ : ((A ∩ B).erase b).Nonempty := ⟨c,hcQ⟩
    have hno : ∀ p ∈ A \ B, ∀ q ∈ (A ∩ B).erase b, ¬ M.Adj p q := by
      intro p hp q hq hadj
      obtain ⟨hqb,hqAB⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqA,hqB⟩ := Finset.mem_inter.mp hqAB
      by_cases hqc : q = c
      · subst q
        exact hnoC p hp (adj_symmetric M hadj)
      · exact (Finset.mem_sdiff.mp hp).2
          (realized_interior_adj_mem M hM RB hqB hqb hqc (adj_symmetric M hadj))
    obtain ⟨_hcP,_hcQ,hcase⟩ := deletion_partition_components M hdelA hbA (Ne.symm hab) hbc
      hcover hdis hP hQ hno
    rcases hcase with ⟨haP,_hcQ'⟩ | ⟨_haQ',hcP⟩
    · exact Finset.disjoint_left.mp hdis haP haQ
    · exact Finset.disjoint_left.mp hdis hcP hcQ
  · intro z hz
    have he := Finset.mem_singleton.mp hz
    subst z
    exact Finset.mem_inter.mpr ⟨RA.joints_mem_ne.2.1,RB.joints_mem_ne.2.1⟩

/-- Once the intersection is a single joint, both realizations must be
blocks: their two joint degrees already exhaust the ambient degree four. -/
theorem realized_single_joint_concatenation (hM : M.IsMolecule) {A B : Finset V} {a b c : V}
    (RA : BlockRealization M A a c) (RB : BlockRealization M B b c) (hi : A ∩ B = {c}) :
    M.IsBlock A a c ∧ M.IsBlock B b c ∧ (M.IsBlock (A ∪ B) a b ∨ IsHyperBlock M (A ∪ B) a b) := by
  have hno : ∀ x, M.atom x = c → M.atom (M.mate x) ≠ c := by
    intro x hx
    have hh := RA.no_joint_loop x (Or.inr hx)
    rw [hx] at hh
    exact hh
  have hdi : M.degIn (A ∩ B) c = 0 := by rw [hi]; exact degIn_singleton_eq_zero M hno
  have hsum := degIn_union_add_inter M A B RA.joints_mem_ne.2.1 RB.joints_mem_ne.2.1
  have hdA := RA.degrees.2.1
  have hdB := RB.degrees.2.1
  have hle := (degIn_le_deg M (A ∪ B) c).trans
    (deg_le_four M hM (RA.atoms_subset RA.joints_mem_ne.2.1))
  have hcA := RA.jointDegree_cases
  have hcB := RB.jointDegree_cases
  have h2a : RA.jointDegree = 2 := by omega
  have h2b : RB.jointDegree = 2 := by omega
  have hA := BlockRealization.isBlock_of_jointDegree_two M RA h2a
  have hB := BlockRealization.isBlock_of_jointDegree_two M RB h2b
  exact ⟨hA,hB,blocks_concatenate M hM hA hB RA.connected hi⟩

end WaveTurbulence.Mole
