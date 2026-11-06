/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.MoleculeCrossedOrdinary
public import WaveTurbulence.Foundations.Spine.MoleculeCrossedPieces
public import WaveTurbulence.Foundations.Spine.MoleculeConnectedInsert
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
import Mathlib.Tactic

/-!
# DH23 Lemma 4.11(c): the actual three-block decomposition

All three pieces are actual induced blocks and connected groups. The
middle piece is exactly the intersection; the exterior pieces are disjoint.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- The complete interleaving decomposition, with actual connected pieces,
after choosing the crossed joint in each of two disjoint joint sets. -/
theorem crossed_three_block_decomposition (hM : M.IsMolecule) {A B : Finset V} {a1 a2 b1 b2 : V}
    (RA : BlockRealization M A a1 a2) (RB : BlockRealization M B b1 b2)
    (hj : Disjoint ({a1,a2} : Finset V) {b1,b2}) (ha1B : a1 ∈ B) (hb1A : b1 ∈ A)
    (hnotA : ¬ A ⊆ B) (hnotB : ¬ B ⊆ A)
    (hdelA : InteriorDeletionProperty M A a1 a2) (hdelB : InteriorDeletionProperty M B b1 b2) :
    M.IsBlock A a1 a2 ∧ M.IsBlock B b1 b2 ∧
      ∃ C0 C1 C2 : Finset V, M.IsBlock C0 a2 b1 ∧ M.IsBlock C1 b1 a1 ∧ M.IsBlock C2 a1 b2 ∧
        GroupConnected M C0 ∧ GroupConnected M C1 ∧ GroupConnected M C2 ∧
        A = C0 ∪ C1 ∧ B = C1 ∪ C2 ∧ C0 ∩ C1 = {b1} ∧ C1 ∩ C2 = {a1} ∧ Disjoint C0 C2 := by
  obtain ⟨hA,hB,ha2out,hb2out,hP0,hQ0,hP2,hQ2⟩ :=
    crossed_joint_structure M hM RA RB hj ha1B hb1A hnotA hnotB hdelA hdelB
  have hcross : ∀ x ∈ ({a1,a2}:Finset V), ∀ y ∈ ({b1,b2}:Finset V), x ≠ y := by
    intro x hx y hy he
    exact Finset.disjoint_left.mp hj hx (he.symm ▸ hy)
  have ha11 : a1 ≠ b1 := hcross a1 (by simp) b1 (by simp)
  have ha12 : a1 ≠ b2 := hcross a1 (by simp) b2 (by simp)
  have hb11 : b1 ≠ a1 := Ne.symm ha11
  have hb12 : b1 ≠ a2 := Ne.symm (hcross a2 (by simp) b1 (by simp))
  let C0 := (A \ B) ∪ {b1}
  let C1 := A ∩ B
  let C2 := (B \ A) ∪ {a1}
  have h0 : M.IsBlock C0 a2 b1 := crossed_left_piece_isBlock M hM hA hB RB.connected
    ha1B ha11 ha12 hb1A hb11 hb12 ha2out hb2out
  have h1 : M.IsBlock C1 a1 b1 := crossed_intersection_isBlock M hM hA hB
    ha1B ha11 ha12 hb1A hb11 hb12 ha2out hb2out
  have h2 : M.IsBlock C2 b2 a1 := crossed_left_piece_isBlock M hM hB hA RA.connected
    hb1A hb11 hb12 ha1B ha11 ha12 hb2out ha2out
  have he0 : C0.erase b1 = A \ B := by
    ext z
    by_cases hz : z = b1
    · subst z
      simp [C0,hB.2.1]
    · simp only [C0,Finset.mem_erase,Finset.mem_union,Finset.mem_sdiff,Finset.mem_singleton]
      tauto
  have he2 : C2.erase a1 = B \ A := by
    ext z
    by_cases hz : z = a1
    · subst z
      simp [C2,hA.2.1]
    · simp only [C2,Finset.mem_erase,Finset.mem_union,Finset.mem_sdiff,Finset.mem_singleton]
      tauto
  have hnoB : ∀ x, M.atom x = b1 → M.atom (M.mate x) ≠ b1 := by
    intro x hx
    have hh := RB.no_joint_loop x (Or.inl hx)
    rw [hx] at hh
    exact hh
  have hnoA : ∀ x, M.atom x = a1 → M.atom (M.mate x) ≠ a1 := by
    intro x hx
    have hh := RA.no_joint_loop x (Or.inl hx)
    rw [hx] at hh
    exact hh
  have hc0 : GroupConnected M C0 := by
    apply connected_of_erase_and_positive_degree M h0.2.2.1
    · rw [he0]
      exact hP0
    · rw [(block_joint_degrees M h0).2]
      decide
    · exact hnoB
  have hc1 : GroupConnected M C1 := by
    apply connected_of_erase_and_positive_degree M h1.2.2.1 hQ0
    · rw [(block_joint_degrees M h1).2]
      decide
    · exact hnoB
  have hc2 : GroupConnected M C2 := by
    apply connected_of_erase_and_positive_degree M h2.2.2.1
    · rw [he2]
      exact hP2
    · rw [(block_joint_degrees M h2).2]
      decide
    · exact hnoA
  have huA : A = C0 ∪ C1 := by
    ext z
    by_cases hz : z = b1
    · subst z
      simp [C0,C1,hb1A,hB.2.1]
    · simp only [C0,C1,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,Finset.mem_singleton]
      tauto
  have huB : B = C1 ∪ C2 := by
    ext z
    by_cases hz : z = a1
    · subst z
      simp [C1,C2,ha1B,hA.2.1]
    · simp only [C1,C2,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,Finset.mem_singleton]
      tauto
  have hi01 : C0 ∩ C1 = {b1} := by
    ext z
    by_cases hz : z = b1
    · subst z
      simp [C0,C1,hb1A,hB.2.1]
    · simp only [C0,C1,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,Finset.mem_singleton]
      tauto
  have hi12 : C1 ∩ C2 = {a1} := by
    ext z
    by_cases hz : z = a1
    · subst z
      simp [C1,C2,ha1B,hA.2.1]
    · simp only [C1,C2,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,Finset.mem_singleton]
      tauto
  have hd02 : Disjoint C0 C2 := by
    apply Finset.disjoint_left.mpr
    intro z hz0 hz2
    rcases Finset.mem_union.mp hz0 with hzP0 | hzb
    · rcases Finset.mem_union.mp hz2 with hzP2 | hza
      · exact (Finset.mem_sdiff.mp hzP0).2 (Finset.mem_sdiff.mp hzP2).1
      · exact (Finset.mem_sdiff.mp hzP0).2 ((Finset.mem_singleton.mp hza).symm ▸ ha1B)
    · have hzb' := Finset.mem_singleton.mp hzb
      rcases Finset.mem_union.mp hz2 with hzP2 | hza
      · exact (Finset.mem_sdiff.mp hzP2).2 (hzb'.symm ▸ hb1A)
      · exact ha11 ((Finset.mem_singleton.mp hza).symm.trans hzb')
  exact ⟨hA,hB,C0,C1,C2,h0,block_swap_joints M h1,block_swap_joints M h2,
    hc0,hc1,hc2,huA,huB,hi01,hi12,hd02⟩

end WaveTurbulence.Mole
