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

end WaveTurbulence.Mole
