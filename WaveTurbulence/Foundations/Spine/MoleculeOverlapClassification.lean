/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.MoleculeThreeBlockDecomposition
public import WaveTurbulence.Foundations.Spine.MoleculeOneJointOverlap
public import WaveTurbulence.Foundations.Spine.MoleculeReorderJoints
import Mathlib.Tactic

/-!
# DH23 Lemma 4.11 / TARGET disjointlem: overlap classification

The block realizations use the explicit connected-adjoint convention.
The three alternatives are separated by their actual joint sets, so their
mutual exclusivity is independent of any choice of decomposition witnesses.
-/

public section
namespace WaveTurbulence.Mole
open Finset
universe u v
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- Actual realization of the three concatenated blocks in the interleaving
alternative. The exterior groups are disjoint and both original joint sets
are identified; no abstract overlap conclusion is stored as a premise. -/
structure ThreeBlockChain (A B JA JB : Finset V) : Type (max u v) where
  C0 : Finset V
  C1 : Finset V
  C2 : Finset V
  p0 : V
  p1 : V
  p2 : V
  p3 : V
  block0 : M.IsBlock C0 p0 p1
  block1 : M.IsBlock C1 p1 p2
  block2 : M.IsBlock C2 p2 p3
  connected0 : GroupConnected M C0
  connected1 : GroupConnected M C1
  connected2 : GroupConnected M C2
  left_union : A = C0 ∪ C1
  right_union : B = C1 ∪ C2
  left_inter : C0 ∩ C1 = {p1}
  right_inter : C1 ∩ C2 = {p2}
  exterior_disjoint : Disjoint C0 C2
  left_joints : JA = {p0,p2}
  right_joints : JB = {p1,p3}

/-- The no-common-joint case, without any ordering assumption on which
joint crosses into the other group. -/
theorem overlap_no_common_joints (hM : M.IsMolecule) {A B : Finset V} {a1 a2 b1 b2 : V}
    (RA : BlockRealization M A a1 a2) (RB : BlockRealization M B b1 b2)
    (hj : Disjoint ({a1,a2}:Finset V) {b1,b2}) (hne : (A ∩ B).Nonempty)
    (hnotA : ¬ A ⊆ B) (hnotB : ¬ B ⊆ A)
    (hdA : InteriorDeletionProperty M A a1 a2) (hdB : InteriorDeletionProperty M B b1 b2)
    (hiA : ∀ x ∈ A \ {a1,a2}, ∀ y ∈ A \ {a1,a2}, (induced M (A \ {a1,a2})).SameComponent x y)
    (hiB : ∀ x ∈ B \ {b1,b2}, ∀ y ∈ B \ {b1,b2}, (induced M (B \ {b1,b2})).SameComponent x y) :
    M.IsBlock A a1 a2 ∧ M.IsBlock B b1 b2 ∧
      Nonempty (ThreeBlockChain M A B {a1,a2} {b1,b2}) := by
  obtain ⟨a,haAB,haj⟩ := overlap_contains_joint M hM RB RA (by rwa [Finset.inter_comm]) hnotB
  obtain ⟨b,hbAB,hbj⟩ := overlap_contains_joint M hM RA RB hne hnotA
  have haB := (Finset.mem_inter.mp haAB).1
  have hbA := (Finset.mem_inter.mp hbAB).1
  have haJ : a ∈ ({a1,a2}:Finset V) := by simpa only [Finset.mem_insert,Finset.mem_singleton] using haj
  have hbJ : b ∈ ({b1,b2}:Finset V) := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hbj
  obtain ⟨a',⟨RA'⟩,heA,hdA',_hiA'⟩ := reorder_joint_first M RA haJ hdA hiA
  obtain ⟨b',⟨RB'⟩,heB,hdB',_hiB'⟩ := reorder_joint_first M RB hbJ hdB hiB
  have hj' : Disjoint ({a,a'}:Finset V) {b,b'} := by rw [← heA,← heB]; exact hj
  obtain ⟨hA,hB,C0,C1,C2,h0,h1,h2,hc0,hc1,hc2,huA,huB,hi01,hi12,hd02⟩ :=
    crossed_three_block_decomposition M hM RA' RB' hj' haB hbA hnotA hnotB hdA' hdB'
  refine ⟨block_transport_joints M heA hA,block_transport_joints M heB hB,?_⟩
  exact ⟨{
    C0 := C0, C1 := C1, C2 := C2
    p0 := a', p1 := b, p2 := a, p3 := b'
    block0 := h0, block1 := h1, block2 := h2
    connected0 := hc0, connected1 := hc1, connected2 := hc2
    left_union := huA, right_union := huB
    left_inter := hi01, right_inter := hi12
    exterior_disjoint := hd02
    left_joints := heA.trans (Finset.pair_comm _ _)
    right_joints := heB }⟩

/-- DH23 Lemma 4.11 / TARGET `disjointlem`: both inputs are blocks and
exactly the shared-two-joint, shared-one-joint, or interleaving alternative
occurs. The mutually exclusive joint-set guards are explicit. -/
theorem molecule_overlap_classification (hM : M.IsMolecule) {A B : Finset V} {a1 a2 b1 b2 : V}
    (RA : BlockRealization M A a1 a2) (RB : BlockRealization M B b1 b2)
    (hne : (A ∩ B).Nonempty) (hnotA : ¬ A ⊆ B) (hnotB : ¬ B ⊆ A)
    (hdA : InteriorDeletionProperty M A a1 a2) (hdB : InteriorDeletionProperty M B b1 b2)
    (hiA : ∀ x ∈ A \ {a1,a2}, ∀ y ∈ A \ {a1,a2}, (induced M (A \ {a1,a2})).SameComponent x y)
    (hiB : ∀ x ∈ B \ {b1,b2}, ∀ y ∈ B \ {b1,b2}, (induced M (B \ {b1,b2})).SameComponent x y) :
    M.IsBlock A a1 a2 ∧ M.IsBlock B b1 b2 ∧
    ((({a1,a2}:Finset V) = {b1,b2} ∧ A ∩ B = {a1,a2} ∧ M.sigma a1 a2 = 1 ∧ M.sigma b1 b2 = 1) ∨
      (({a1,a2}:Finset V) ≠ {b1,b2} ∧ ¬ Disjoint ({a1,a2}:Finset V) {b1,b2} ∧
        ∃ a b c : V, ({a1,a2}:Finset V) = {a,c} ∧ ({b1,b2}:Finset V) = {b,c} ∧
          a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ A ∩ B = {c} ∧
          (M.IsBlock (A ∪ B) a b ∨ IsHyperBlock M (A ∪ B) a b)) ∨
      (Disjoint ({a1,a2}:Finset V) {b1,b2} ∧ Nonempty (ThreeBlockChain M A B {a1,a2} {b1,b2}))) := by
  by_cases hj : ({a1,a2}:Finset V) = {b1,b2}
  · rcases finset_pair_eq_pair_iff.mp hj with ⟨h11,h22⟩ | ⟨h12,h21⟩
    · subst b1
      subst b2
      obtain ⟨hA,hB,hi,hs⟩ := realized_same_joints_classification M hM RA RB hnotA hnotB hiA
      exact ⟨hA,hB,Or.inl ⟨hj,hi,hs,hs⟩⟩
    · subst b1
      subst b2
      obtain ⟨hA,hB,hi,hs⟩ := realized_same_joints_classification M hM RA RB.swap hnotA hnotB hiA
      exact ⟨hA,block_swap_joints M hB,Or.inl ⟨hj,hi,hs,(bondsBetween_symm M _ _).trans hs⟩⟩
  · by_cases hdis : Disjoint ({a1,a2}:Finset V) {b1,b2}
    · obtain ⟨hA,hB,hchain⟩ := overlap_no_common_joints M hM RA RB hdis hne hnotA hnotB hdA hdB hiA hiB
      exact ⟨hA,hB,Or.inr (Or.inr ⟨hdis,hchain⟩)⟩
    · obtain ⟨c,hcA,hcB⟩ := Finset.not_disjoint_iff.mp hdis
      obtain ⟨a,⟨RA'⟩,heA,hdA',hiA'⟩ := reorder_joint_second M RA hcA hdA hiA
      obtain ⟨b,⟨RB'⟩,heB,hdB',hiB'⟩ := reorder_joint_second M RB hcB hdB hiB
      have hab : a ≠ b := by intro he; apply hj; rw [heA,heB,he]
      have hi := realized_one_joint_intersection M hM RA' RB' hab hnotA hnotB hiA' hiB' hdA'
      obtain ⟨hA,hB,hconcat⟩ := realized_single_joint_concatenation M hM RA' RB' hi
      exact ⟨block_transport_joints M heA hA,block_transport_joints M heB hB,
        Or.inr (Or.inl ⟨hj,hdis,a,b,c,heA,heB,hab,RA'.joints_mem_ne.2.2,RB'.joints_mem_ne.2.2,hi,hconcat⟩)⟩

end WaveTurbulence.Mole
