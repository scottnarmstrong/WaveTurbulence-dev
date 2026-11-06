/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.MoleculeOverlapDeletion
public import WaveTurbulence.Foundations.Spine.MoleculeFullIntersections
import Mathlib.Tactic

/-!
# Hyper-block exclusion and component structure for crossed joint sets

DH23 Lemma 4.11(2): source deletion properties force the other two joints
outside the opposite groups. Their added hyper-block bonds would then
cross a full-degree boundary, so both realizations are ordinary blocks.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- The complete ordinary-block and connected-piece consequences in the
no-common-joint case, after choosing one crossed joint in each direction. -/
theorem crossed_joint_structure (hM : M.IsMolecule) {A B : Finset V} {a1 a2 b1 b2 : V}
    (RA : BlockRealization M A a1 a2) (RB : BlockRealization M B b1 b2)
    (hj : Disjoint ({a1,a2} : Finset V) {b1,b2}) (ha1B : a1 ∈ B) (hb1A : b1 ∈ A)
    (hnotA : ¬ A ⊆ B) (hnotB : ¬ B ⊆ A)
    (hdelA : InteriorDeletionProperty M A a1 a2) (hdelB : InteriorDeletionProperty M B b1 b2) :
    M.IsBlock A a1 a2 ∧ M.IsBlock B b1 b2 ∧ a2 ∉ B ∧ b2 ∉ A ∧
      GroupConnected M (A \ B) ∧ GroupConnected M ((A ∩ B).erase b1) ∧
      GroupConnected M (B \ A) ∧ GroupConnected M ((B ∩ A).erase a1) := by
  have hcross : ∀ x ∈ ({a1,a2}:Finset V), ∀ y ∈ ({b1,b2}:Finset V), x ≠ y := by
    intro x hx y hy he
    exact Finset.disjoint_left.mp hj hx (he.symm ▸ hy)
  have ha11 : a1 ≠ b1 := hcross a1 (by simp) b1 (by simp)
  have ha12 : a1 ≠ b2 := hcross a1 (by simp) b2 (by simp)
  have hb11 : b1 ≠ a1 := Ne.symm ha11
  have hb12 : b1 ≠ a2 := Ne.symm (hcross a2 (by simp) b1 (by simp))
  have hb2out : b2 ∉ A := by
    intro hb2A
    have ha2out : a2 ∉ B := fun ha2B => not_all_joints_cross M hM RA RB hj ha1B ha2B hb1A hb2A
    have hsep := overlap_deletion_partition M hM RB RA hdelB hnotB hb1A ha1B ha11 ha12 ha2out
    exact (Finset.mem_sdiff.mp hsep.2.2.1).2 hb2A
  have hsepA := overlap_deletion_partition M hM RA RB hdelA hnotA ha1B hb1A hb11 hb12 hb2out
  have ha2out := (Finset.mem_sdiff.mp hsepA.2.2.1).2
  have hsepB := overlap_deletion_partition M hM RB RA hdelB hnotB hb1A ha1B ha11 ha12 ha2out
  have hA := realization_block_of_crossed_joints M hM RA RB ha1B ha11 ha12 ha2out
  have hB := realization_block_of_crossed_joints M hM RB RA hb1A hb11 hb12 hb2out
  exact ⟨hA,hB,ha2out,hb2out,hsepA.1,hsepA.2.1,hsepB.1,hsepB.2.1⟩

end WaveTurbulence.Mole
