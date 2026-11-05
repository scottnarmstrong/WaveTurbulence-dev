/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockChains
import Mathlib.Tactic

/-! # Actual simultaneous block deletion
TARGET `cnblock`: remove precisely all nonjoint atoms and all internal
bonds of the selected blocks. Joints remain unless removed by another
block; disjointness will exclude that latter possibility.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

/-- Nonjoint atoms removed by a finite family of actual blocks. -/
@[expose] noncomputable def removedBlockInteriors (F : Finset (GardenBlockSegment G)) :
    Finset (GBranch G.tree) := by
  classical
  exact F.biUnion (fun B => B.atoms \ {B.leftJoint,B.rightJoint})

theorem mem_removedBlockInteriors (F : Finset (GardenBlockSegment G)) (v : GBranch G.tree) :
    v ∈ removedBlockInteriors G F ↔ ∃ B ∈ F, v ∈ B.atoms ∧ v ≠ B.leftJoint ∧ v ≠ B.rightJoint := by
  classical
  simp only [removedBlockInteriors,mem_biUnion,mem_sdiff,mem_insert,mem_singleton,not_or]

/-- Exactly the old darts whose bonds are not internal to any removed block. -/
abbrev BlockFamilyDart (F : Finset (GardenBlockSegment G)) :=
  {x : GardenDart G // ∀ B ∈ F, ¬ G.molecule.InGroup B.atoms x}

theorem blockFamilyDart_mate {F : Finset (GardenBlockSegment G)} (x : BlockFamilyDart G F) :
    ∀ B ∈ F, ¬ G.molecule.InGroup B.atoms (G.molecule.mate x.1) := by
  intro B hB hi
  exact x.2 B hB ⟨by simpa only [G.molecule.mate_mate] using hi.2,hi.1⟩

/-- The actual result of simultaneous block removal, on the literal
surviving atom and half-edge carriers. -/
@[expose] noncomputable def removeBlockFamily (F : Finset (GardenBlockSegment G)) :
    Molecule (GBranch G.tree) (BlockFamilyDart G F) where
  atoms := G.molecule.atoms \ removedBlockInteriors G F
  atom x := G.molecule.atom x.1
  mate x := ⟨G.molecule.mate x.1,blockFamilyDart_mate G x⟩
  out x := G.molecule.out x.1
  atom_mem x := by
    refine mem_sdiff.mpr ⟨G.molecule.atom_mem x.1,?_⟩
    intro hr
    obtain ⟨B,hBF,hv,hl,hr⟩ := (mem_removedBlockInteriors G F _).mp hr
    have hd := B.block.2.2.2.2.2.2.2.2.1 _ hv hl hr
    have hm := full_degree_no_exit G.molecule (garden_isMolecule G)
      (G.molecule.atom_mem x.1) hd (x := x.1) rfl
    exact x.2 B hBF ⟨hv,hm⟩
  mate_mate x := Subtype.ext (G.molecule.mate_mate x.1)
  mate_ne x h := G.molecule.mate_ne x.1 (congrArg Subtype.val h)
  out_mate x := G.molecule.out_mate x.1

end WaveTurbulence.Mole
