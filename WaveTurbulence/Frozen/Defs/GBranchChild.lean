/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GBranch
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeBranching
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.TTreePre

/-!
# GBranch.child

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

/-- The `i`-th child (`0, 1, 2` = left, mid, right) of a branching node. -/
def GBranch.child (b : GBranch tree) (i : Fin 3) : GNode tree :=
  ⟨(b.1.1, b.1.2 ++ [i]), by
    have cons_mem : ∀ (i j : Fin 3) (S : Finset TTree.Path) (q : TTree.Path),
        j :: q ∈ TTree.pre i S ↔ i = j ∧ q ∈ S := by
      intro i j S q
      simp only [TTree.pre, Finset.mem_image, List.cons.injEq]
      constructor
      · rintro ⟨q', hq', rfl, rfl⟩
        exact ⟨rfl, hq'⟩
      · rintro ⟨rfl, hq⟩
        exact ⟨q, hq, rfl, rfl⟩
    have key : ∀ (t : TTree) (p : TTree.Path), p ∈ t.branching → ∀ i : Fin 3,
        p ++ [i] ∈ t.nodes := by
      intro t
      induction t with
      | leaf => exact fun p hp => by simp [TTree.branching] at hp
      | node l m r ihl ihm ihr =>
        intro p hp i
        rcases p with _ | ⟨j, p⟩
        · have hnil : ∀ s : TTree, ([] : TTree.Path) ∈ s.nodes := fun s => by
            cases s <;> simp [TTree.nodes]
          simp only [List.nil_append, TTree.nodes, Finset.mem_insert, Finset.mem_union, cons_mem]
          fin_cases i <;> simp [hnil]
        · simp only [TTree.branching, Finset.mem_insert, Finset.mem_union, cons_mem, reduceCtorEq,
            false_or] at hp
          simp only [List.cons_append, TTree.nodes, Finset.mem_insert, Finset.mem_union, cons_mem,
            reduceCtorEq, false_or]
          rcases hp with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩
          · exact Or.inl (Or.inl ⟨rfl, ihl p h i⟩)
          · exact Or.inl (Or.inr ⟨rfl, ihm p h i⟩)
          · exact Or.inr ⟨rfl, ihr p h i⟩
    exact key _ _ b.2 i⟩

end Forest
end WaveTurbulence
