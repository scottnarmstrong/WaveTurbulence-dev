/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.ChainParentTransfer
import Mathlib.Tactic

/-! # A concatenated block containing a CN ingredient has the CN parent pattern -/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} (G : Garden w)

theorem cnSegmentCount_pos_of_member (blocks : List (GardenBlockSegment G))
    (B : GardenBlockSegment G) (hB : B ∈ blocks)
    (hCN : CNParentPattern G B.atoms B.leftJoint B.rightJoint) : 0 < cnSegmentCount G blocks := by
  classical
  cases blocks with
  | nil => exact (List.not_mem_nil hB).elim
  | cons A rest =>
    rw [cnSegmentCount]
    rcases List.mem_cons.mp hB with he | ht
    · subst B
      rw [ite_eq_left hCN]
      omega
    · have hp := cnSegmentCount_pos_of_member rest B ht hCN
      omega
termination_by blocks.length

theorem chain_right_parent_forces_no_cn (A : GardenBlockSegment G) (rest : List (GardenBlockSegment G))
    (hc : (A :: rest).IsChain (SegmentFollows G))
    (hr : InternalParent G ((A :: rest).getLast (List.cons_ne_nil _ _)).atoms
      ((A :: rest).getLast (List.cons_ne_nil _ _)).rightJoint) :
    InternalParent G A.atoms A.rightJoint ∧ cnSegmentCount G (A :: rest) = 0 := by
  classical
  cases rest with
  | nil =>
    have hA : InternalParent G A.atoms A.rightJoint := hr
    refine ⟨hA,?_⟩
    have hn : ¬ CNParentPattern G A.atoms A.leftJoint A.rightJoint := fun h => h.2 hA
    rw [cnSegmentCount,ite_eq_right hn,cnSegmentCount]
  | cons B tail =>
    obtain ⟨hf,ht⟩ := List.isChain_cons_cons.mp hc
    obtain ⟨hB,hzero⟩ := chain_right_parent_forces_no_cn B tail ht hr
    have hBL : ¬ InternalParent G B.atoms B.leftJoint := fun h => segment_parent_exclusion G B h hB
    have hA := (segment_shared_parent G hf).resolve_right hBL
    refine ⟨hA,?_⟩
    have hn : ¬ CNParentPattern G A.atoms A.leftJoint A.rightJoint := fun h => h.2 hA
    rw [cnSegmentCount,ite_eq_right hn,zero_add,hzero]
termination_by rest.length

/-- Source `blockchainprop`: in the one-CN case both outer joint parents
are outside the concatenated block, before any splicing is performed. -/
theorem chain_with_cn_parent_pattern (A : GardenBlockSegment G) (rest : List (GardenBlockSegment G))
    (whole : Finset (GBranch G.tree)) (hc : (A :: rest).IsChain (SegmentFollows G))
    (hsub : ∀ B ∈ A :: rest, B.atoms ⊆ whole)
    (hwhole : G.molecule.IsBlock whole A.leftJoint
      ((A :: rest).getLast (List.cons_ne_nil _ _)).rightJoint)
    (B : GardenBlockSegment G) (hB : B ∈ A :: rest)
    (hCN : CNParentPattern G B.atoms B.leftJoint B.rightJoint) :
    CNParentPattern G whole A.leftJoint ((A :: rest).getLast (List.cons_ne_nil _ _)).rightJoint := by
  let last := (A :: rest).getLast (List.cons_ne_nil _ _)
  have hl : last ∈ A :: rest := List.getLast_mem _
  have hleft := internalParent_eq_of_degree_eq G (hsub A List.mem_cons_self) A.block.2.1
    ((block_joint_degrees G.molecule A.block).1.trans (block_joint_degrees G.molecule hwhole).1.symm)
  have hright := internalParent_eq_of_degree_eq G (hsub last hl) last.block.2.2.1
    ((block_joint_degrees G.molecule last.block).2.trans (block_joint_degrees G.molecule hwhole).2.symm)
  have hpos := cnSegmentCount_pos_of_member G (A :: rest) B hB hCN
  constructor
  · intro hp
    have hz := chain_no_cn_of_left_parent G A rest hc (hleft.mpr hp)
    omega
  · intro hp
    have hz := (chain_right_parent_forces_no_cn G A rest hc (hright.mpr hp)).2
    omega

end WaveTurbulence.Mole
