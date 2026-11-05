/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockRemovalDegrees
import Mathlib.Tactic

/-! # Degree-two joints remain and become isolated
TARGET `cnblock`: disjointness keeps each joint, and its two old internal
incidences exhaust the ambient degree. This supplies the isolated atom
used to charge zero-deficit components.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w) (F : Finset (GardenBlockSegment G))

theorem block_family_joint_survives
    (hdis : Set.PairwiseDisjoint (F : Set (GardenBlockSegment G)) GardenBlockSegment.atoms)
    (B : GardenBlockSegment G) (hB : B ∈ F) (v : GBranch G.tree)
    (hv : v = B.leftJoint ∨ v = B.rightJoint) : v ∉ removedBlockInteriors G F := by
  intro hr
  obtain ⟨C,hC,hvC,hneL,hneR⟩ := (mem_removedBlockInteriors G F v).mp hr
  have hvB : v ∈ B.atoms := by
    rcases hv with rfl | rfl
    · exact B.block.2.1
    · exact B.block.2.2.1
  have he : C = B := by
    by_contra hn
    exact Finset.disjoint_left.mp (hdis hC hB hn) hvC hvB
  subst C
  rcases hv with he | he
  · exact hneL he
  · exact hneR he

/-- Any degree-two joint of a removed block is an actual surviving isolated atom. -/
theorem block_family_degree_two_joint_isolated
    (hdis : Set.PairwiseDisjoint (F : Set (GardenBlockSegment G)) GardenBlockSegment.atoms)
    (B : GardenBlockSegment G) (hB : B ∈ F) (v : GBranch G.tree)
    (hv : v = B.leftJoint ∨ v = B.rightJoint) (hd : G.molecule.deg v = 2) :
    v ∈ (removeBlockFamily G F).atoms ∧ (removeBlockFamily G F).deg v = 0 := by
  have hvB : v ∈ B.atoms := by
    rcases hv with rfl | rfl
    · exact B.block.2.1
    · exact B.block.2.2.1
  have hi : G.molecule.degIn B.atoms v = 2 := by
    have h := block_joint_degrees G.molecule B.block
    rcases hv with rfl | rfl
    · exact h.1
    · exact h.2
  have hc : (removedDartsAt G F v).card = 2 := by
    rw [removedDartsAt_eq_block G F hdis B hB v hvB]
    exact hi
  have hsum := degree_add_removedDartsAt G F v
  refine ⟨mem_sdiff.mpr ⟨mem_univ _,block_family_joint_survives G F hdis B hB v hv⟩,?_⟩
  omega

end WaveTurbulence.Mole
