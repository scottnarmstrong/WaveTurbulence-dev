/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockFamilyRemoval
import Mathlib.Tactic

/-! # CN deletion preserves all surviving tree-parent edges
TARGET `cnblock`: actual residual atoms remain connected to the original
branching root of their tree. No component bound is assumed.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w) (F : Finset (GardenBlockSegment G))
variable (hCN : ∀ B ∈ F, CNParentPattern G B.atoms B.leftJoint B.rightJoint)
include hCN

theorem cn_parent_dart_survives (c : GBranch G.tree) (hc : c ∉ removedBlockInteriors G F)
    (hn : c.1.2 ≠ []) :
    ∀ B ∈ F, ¬ G.molecule.InGroup B.atoms (.inl (⟨c,hn⟩,false)) := by
  intro B hBF hinside
  have hv : c ∈ B.atoms := hinside.1
  have hp : GNode.parent c.toNode hn ∈ B.atoms := hinside.2
  have hj : c = B.leftJoint ∨ c = B.rightJoint := by
    by_contra hj
    push Not at hj
    exact hc ((mem_removedBlockInteriors G F c).mpr ⟨B,hBF,hv,hj.1,hj.2⟩)
  rcases hj with he | he
  · exact (hCN B hBF).1 (he ▸ (show InternalParent G B.atoms c from ⟨hn,hp⟩))
  · exact (hCN B hBF).2 (he ▸ (show InternalParent G B.atoms c from ⟨hn,hp⟩))

theorem cn_parent_adj (c : GBranch G.tree) (hc : c ∉ removedBlockInteriors G F)
    (hn : c.1.2 ≠ []) :
    (removeBlockFamily G F).Adj c (GNode.parent c.toNode hn) := by
  exact ⟨⟨.inl (⟨c,hn⟩,false),cn_parent_dart_survives G F hCN c hc hn⟩,rfl,rfl⟩

theorem cn_parent_not_removed (c : GBranch G.tree) (hc : c ∉ removedBlockInteriors G F)
    (hn : c.1.2 ≠ []) : GNode.parent c.toNode hn ∉ removedBlockInteriors G F := by
  let x : BlockFamilyDart G F := ⟨.inl (⟨c,hn⟩,false),cn_parent_dart_survives G F hCN c hc hn⟩
  exact (mem_sdiff.mp ((removeBlockFamily G F).atom_mem ((removeBlockFamily G F).mate x))).2

/-- Each actual residual atom reaches its original tree root using
surviving original PC bonds. This is stronger than a root-label assignment. -/
theorem cn_residual_connected_root (c : GBranch G.tree) (hc : c ∉ removedBlockInteriors G F) :
    (removeBlockFamily G F).SameComponent c (branchRoot c) := by
  by_cases hn : c.1.2 = []
  · have he : c = branchRoot c := Subtype.ext (Prod.ext rfl hn)
    exact he ▸ sameComponent_refl (removeBlockFamily G F) c
  · let p := GNode.parent c.toNode hn
    have hp := cn_residual_connected_root p (cn_parent_not_removed G F hCN c hc hn)
    have he : branchRoot p = branchRoot c := Subtype.ext rfl
    rw [he] at hp
    exact sameComponent_trans (removeBlockFamily G F)
      (sameComponent_of_adj (removeBlockFamily G F) (cn_parent_adj G F hCN c hc hn)) hp
termination_by c.1.2.length
decreasing_by
  dsimp only [p,GNode.parent,GBranch.toNode]
  rw [List.length_dropLast]
  have hp := List.length_pos_of_ne_nil hn
  omega

end WaveTurbulence.Mole
