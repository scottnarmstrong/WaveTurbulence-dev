/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegionIncidences
public import WaveTurbulence.Foundations.Molecule.MoleculeBlockConcatenation
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
import Mathlib.Tactic

/-! # The unique-CN principle for chains of actual connected blocks

TARGET `blockchainprop`, first assertion (DH23 Corollary 4.13).
Here CN is the intrinsic parent pattern; the geometric equivalence is
kept separate. No property of a putative CN count is a hypothesis.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

/-- A connected block with its joints ordered along a chain. -/
structure GardenBlockSegment where
  atoms : Finset (GBranch G.tree)
  leftJoint : GBranch G.tree
  rightJoint : GBranch G.tree
  block : G.molecule.IsBlock atoms leftJoint rightJoint
  connected : GroupConnected G.molecule atoms

/-- Adjacent ingredients have precisely their common joint in common. -/
@[expose] def SegmentFollows (A B : GardenBlockSegment G) : Prop :=
  A.rightJoint = B.leftJoint ∧ A.atoms ∩ B.atoms = {A.rightJoint}

theorem segment_shared_parent {A B : GardenBlockSegment G} (hf : SegmentFollows G A B) :
    InternalParent G A.atoms A.rightJoint ∨ InternalParent G B.atoms B.leftJoint := by
  have hB : G.molecule.IsBlock B.atoms B.rightJoint A.rightJoint := by
    rw [hf.1]
    exact block_swap_joints G.molecule B.block
  have hd := concatenation_common_degree G.molecule A.block hB A.connected hf.2
  obtain ⟨hn,hp⟩ := full_internal_has_parent G hd
  rcases mem_union.mp hp with hpa | hpb
  · exact Or.inl ⟨hn,hpa⟩
  · right
    rw [← hf.1]
    exact ⟨hn,hpb⟩

theorem segment_parent_exclusion (A : GardenBlockSegment G) :
    InternalParent G A.atoms A.leftJoint → ¬ InternalParent G A.atoms A.rightJoint := by
  have h := block_parent_dichotomy G A.block
  tauto

/-- Number of ingredients having the intrinsic CN pattern. -/
@[expose] noncomputable def cnSegmentCount : List (GardenBlockSegment G) → ℕ
  | [] => 0
  | A :: rest => by
      classical
      exact (if CNParentPattern G A.atoms A.leftJoint A.rightJoint then 1 else 0) +
        cnSegmentCount rest

/-- An incoming parent at the first left joint propagates across the whole chain. -/
theorem chain_no_cn_of_left_parent (A : GardenBlockSegment G) (rest : List (GardenBlockSegment G))
    (hc : (A :: rest).IsChain (SegmentFollows G))
    (hp : InternalParent G A.atoms A.leftJoint) : cnSegmentCount G (A :: rest) = 0 := by
  classical
  have hn : ¬ CNParentPattern G A.atoms A.leftJoint A.rightJoint := fun h => h.1 hp
  rw [cnSegmentCount,ite_eq_right hn,zero_add]
  cases rest with
  | nil => rfl
  | cons B tail =>
    obtain ⟨hf,ht⟩ := List.isChain_cons_cons.mp hc
    have hright := segment_parent_exclusion G A hp
    have hleft := (segment_shared_parent G hf).resolve_left hright
    exact chain_no_cn_of_left_parent B tail ht hleft
termination_by rest.length

/-- At most one ingredient of an actual connected block chain has the CN parent pattern.
This needs only adjacent intersections, so also applies to hyper-block chains. -/
theorem chain_at_most_one_cn (blocks : List (GardenBlockSegment G))
    (hc : blocks.IsChain (SegmentFollows G)) : cnSegmentCount G blocks ≤ 1 := by
  classical
  cases blocks with
  | nil => exact Nat.zero_le _
  | cons A rest =>
    by_cases hn : CNParentPattern G A.atoms A.leftJoint A.rightJoint
    · rw [cnSegmentCount,ite_eq_left hn]
      cases rest with
      | nil => simp only [cnSegmentCount,add_zero,le_refl]
      | cons B tail =>
        obtain ⟨hf,ht⟩ := List.isChain_cons_cons.mp hc
        have hp := (segment_shared_parent G hf).resolve_left hn.2
        rw [chain_no_cn_of_left_parent G B tail ht hp]
    · rw [cnSegmentCount,ite_eq_right hn,zero_add]
      exact chain_at_most_one_cn rest hc.tail
termination_by blocks.length

end WaveTurbulence.Mole
