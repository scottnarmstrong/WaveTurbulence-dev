/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GLeaf
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeLeaves
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath

/-!
# GLeaf.toNode

Wave B tier B1 (WaveB1-Core.lean), source: (section) T Def `defgarden`, L632–L638. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

section Forest

open TTree
variable {w : ℕ} (tree : Fin w → TTree)
variable {tree}

/-- A leaf as a node. -/
def GLeaf.toNode (ℓ : GLeaf tree) : GNode tree :=
  ⟨ℓ.1, by
    have key : ∀ (t : TTree) (p : TTree.Path), p ∈ t.leaves → p ∈ t.nodes := by
      intro t
      induction t with
      | leaf => exact fun p hp => by simpa [TTree.leaves, TTree.nodes] using hp
      | node l m r ihl ihm ihr =>
        intro p hp
        simp only [TTree.leaves, TTree.pre, Finset.mem_union, Finset.mem_image] at hp
        simp only [TTree.nodes, TTree.pre, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        rcases hp with (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩
        · exact Or.inr (Or.inl (Or.inl ⟨q, ihl q hq, rfl⟩))
        · exact Or.inr (Or.inl (Or.inr ⟨q, ihm q hq, rfl⟩))
        · exact Or.inr (Or.inr ⟨q, ihr q hq, rfl⟩)
    exact key _ _ ℓ.2⟩

end Forest
end WaveTurbulence
