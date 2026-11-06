/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.MoleculeOverlapCrossings
import Mathlib.Tactic

/-!
# Deletion partitions forced by crossed joints

DH23 Lemma 4.11(2): deleting the joint of B inside A separates A outside B
from its intersection with B. The source deletion premise then forces the
two original joints of A into different actual components.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

omit [Fintype D] [DecidableEq D] in
/-- The actual deletion premise identifies both sides of any nonempty
empty-edge cut as its two components, and separates the original joints. -/
theorem deletion_partition_components {A P Q : Finset V} {a1 a2 v : V}
    (hdel : InteriorDeletionProperty M A a1 a2) (hv : v ∈ A) (h1 : v ≠ a1) (h2 : v ≠ a2)
    (hcover : P ∪ Q = A.erase v) (hdis : Disjoint P Q) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hno : ∀ p ∈ P, ∀ q ∈ Q, ¬ M.Adj p q) :
    GroupConnected M P ∧ GroupConnected M Q ∧ ((a1 ∈ P ∧ a2 ∈ Q) ∨ (a1 ∈ Q ∧ a2 ∈ P)) := by
  rcases hdel v hv h1 h2 with hc | ht
  · exact (not_connected_of_partition M hcover hdis hP hQ hno hc).elim
  · exact two_components_partition M hcover hdis hP hQ hno ht

/-- The crossed-joint situation in DH23 Lemma 4.11(2) gives the exact
connected partition of A after removing the interior joint b1. -/
theorem overlap_deletion_partition (hM : M.IsMolecule) {A B : Finset V} {a1 a2 b1 b2 : V}
    (RA : BlockRealization M A a1 a2) (RB : BlockRealization M B b1 b2)
    (hdel : InteriorDeletionProperty M A a1 a2) (hnot : ¬ A ⊆ B)
    (ha1B : a1 ∈ B) (hb1A : b1 ∈ A) (hb11 : b1 ≠ a1) (hb12 : b1 ≠ a2)
    (hb2out : b2 ∉ A) :
    GroupConnected M (A \ B) ∧ GroupConnected M ((A ∩ B).erase b1) ∧
      a2 ∈ A \ B ∧ a1 ∈ (A ∩ B).erase b1 := by
  have hjA := RA.joints_mem_ne
  have hjB := RB.joints_mem_ne
  have hcover : (A \ B) ∪ (A ∩ B).erase b1 = A.erase b1 := by
    ext z
    by_cases hz : z = b1
    · subst z
      simp [hjB.1]
    · simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,Finset.mem_erase]
      tauto
  have hdis : Disjoint (A \ B) ((A ∩ B).erase b1) := by
    apply Finset.disjoint_left.mpr
    intro z hzP hzQ
    exact (Finset.mem_sdiff.mp hzP).2 (Finset.mem_inter.mp (Finset.mem_erase.mp hzQ).2).2
  have hP : (A \ B).Nonempty := by
    obtain ⟨z,hzA,hzB⟩ := Finset.not_subset.mp hnot
    exact ⟨z,Finset.mem_sdiff.mpr ⟨hzA,hzB⟩⟩
  have ha1Q : a1 ∈ (A ∩ B).erase b1 :=
    Finset.mem_erase.mpr ⟨Ne.symm hb11,Finset.mem_inter.mpr ⟨hjA.1,ha1B⟩⟩
  have hQ : ((A ∩ B).erase b1).Nonempty := ⟨a1,ha1Q⟩
  have hno : ∀ p ∈ A \ B, ∀ q ∈ (A ∩ B).erase b1, ¬ M.Adj p q := by
    intro p hp q hq hadj
    obtain ⟨hpA,hpB⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hqb1,hqAB⟩ := Finset.mem_erase.mp hq
    obtain ⟨hqA,hqB⟩ := Finset.mem_inter.mp hqAB
    have hqb2 : q ≠ b2 := fun he => hb2out (he ▸ hqA)
    exact hpB (realized_interior_adj_mem M hM RB hqB hqb1 hqb2 (adj_symmetric M hadj))
  obtain ⟨hcP,hcQ,hcase⟩ := deletion_partition_components M hdel hb1A hb11 hb12 hcover hdis hP hQ hno
  refine ⟨hcP,hcQ,?_,ha1Q⟩
  rcases hcase with ⟨ha1P,ha2Q⟩ | ⟨ha1Q',ha2P⟩
  · exact (Finset.disjoint_left.mp hdis ha1P ha1Q).elim
  · exact ha2P

end WaveTurbulence.Mole
