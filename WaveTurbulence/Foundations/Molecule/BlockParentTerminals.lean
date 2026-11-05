/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockFamilyRemoval
import Mathlib.Tactic

/-! # Parent paths after CN and root-CL removal
TARGET `cnblock`: a surviving parent path stops only at an original root
or at the lower joint of a removed CL block.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

/-- The precise two source types allowed in `cnblock`, with CL joints
ordered upper/lower. CN is independent of that ordering. -/
@[expose] def IsCNOrRootCL (B : GardenBlockSegment G) : Prop :=
  CNParentPattern G B.atoms B.leftJoint B.rightJoint ∨
    (CLParentPattern G B.atoms B.leftJoint B.rightJoint ∧
      G.molecule.deg B.leftJoint + G.molecule.deg B.rightJoint ≤ 6)

variable (F : Finset (GardenBlockSegment G))
variable (hkind : ∀ B ∈ F, IsCNOrRootCL G B)
include hkind

theorem residual_parent_terminal (v : GBranch G.tree) (hv : v ∉ removedBlockInteriors G F) :
    ∃ z : GBranch G.tree, z ∉ removedBlockInteriors G F ∧
      (removeBlockFamily G F).SameComponent v z ∧
      (z.1.2 = [] ∨ ∃ B ∈ F, z = B.rightJoint ∧
        CLParentPattern G B.atoms B.leftJoint B.rightJoint ∧
        G.molecule.deg B.leftJoint + G.molecule.deg B.rightJoint ≤ 6) := by
  classical
  by_cases hn : v.1.2 = []
  · exact ⟨v,hv,sameComponent_refl _ v,Or.inl hn⟩
  let x : GardenDart G := .inl (⟨v,hn⟩,false)
  by_cases hx : ∀ B ∈ F, ¬ G.molecule.InGroup B.atoms x
  · let y : BlockFamilyDart G F := ⟨x,hx⟩
    let p := GNode.parent v.toNode hn
    have hp : p ∉ removedBlockInteriors G F :=
      (mem_sdiff.mp ((removeBlockFamily G F).atom_mem ((removeBlockFamily G F).mate y))).2
    obtain ⟨z,hz,hpz,ht⟩ := residual_parent_terminal p hp
    refine ⟨z,hz,sameComponent_trans _ ?_ hpz,ht⟩
    exact sameComponent_of_adj _ ⟨y,rfl,rfl⟩
  · push Not at hx
    obtain ⟨B,hBF,hinside⟩ := hx
    have hb : v ∈ B.atoms := hinside.1
    have hp : GNode.parent v.toNode hn ∈ B.atoms := hinside.2
    have hj : v = B.leftJoint ∨ v = B.rightJoint := by
      by_contra hj
      push Not at hj
      exact hv ((mem_removedBlockInteriors G F v).mpr ⟨B,hBF,hb,hj.1,hj.2⟩)
    have hleft : ¬ InternalParent G B.atoms B.leftJoint := by
      rcases hkind B hBF with h | h
      · exact h.1
      · exact h.1.1
    have hir : InternalParent G B.atoms v := ⟨hn,hp⟩
    rcases hj with he | he
    · exact (hleft (he ▸ hir)).elim
    · rcases hkind B hBF with hCN | hCL
      · exact (hCN.2 (he ▸ hir)).elim
      · exact ⟨v,hv,sameComponent_refl _ v,Or.inr ⟨B,hBF,he,hCL.1,hCL.2⟩⟩
termination_by v.1.2.length
decreasing_by
  dsimp only [p,GNode.parent,GBranch.toNode]
  rw [List.length_dropLast]
  have hp := List.length_pos_of_ne_nil hn
  omega

end WaveTurbulence.Mole
