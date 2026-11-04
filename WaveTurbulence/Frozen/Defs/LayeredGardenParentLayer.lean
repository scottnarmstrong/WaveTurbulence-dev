/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.TTreePre

/-!
# LayeredGarden.parentLayer

Wave B tier B1 (WaveB1-Core.lean), source: T Prop `canonequiv`. Frozen by ruling D7
(`docs/DECISIONS.md#D7`); do not edit.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The layer of the parent of `a`, the parent layer of a root being read as `top`
(T Prop `canonequiv`: "replaced by `p`"). -/
def parentLayer (top : ℕ) (a : GNode LG.garden.tree) : ℕ :=
  if a.1.2 = [] then top
  else LG.layer ⟨(a.1.1, a.1.2.dropLast), by
    have cons_mem : ∀ (i j : Fin 3) (S : Finset TTree.Path) (q : TTree.Path),
        j :: q ∈ TTree.pre i S ↔ i = j ∧ q ∈ S := by
      intro i j S q
      simp only [TTree.pre, Finset.mem_image, List.cons.injEq]
      constructor
      · rintro ⟨q', hq', rfl, rfl⟩
        exact ⟨rfl, hq'⟩
      · rintro ⟨rfl, hq⟩
        exact ⟨q, hq, rfl, rfl⟩
    have key : ∀ (t : TTree) (p : TTree.Path), p ∈ t.nodes → p.dropLast ∈ t.nodes := by
      intro t
      induction t with
      | leaf =>
        intro p h
        simp only [TTree.nodes, Finset.mem_singleton] at h
        subst h
        simp [TTree.nodes]
      | node l m r ihl ihm ihr =>
        intro p h
        rcases p with _ | ⟨j, p⟩
        · simp [TTree.nodes]
        · simp only [TTree.nodes, Finset.mem_insert, Finset.mem_union, cons_mem, reduceCtorEq,
            false_or] at h
          rcases p with _ | ⟨c, p⟩
          · simp [TTree.nodes]
          · rw [List.dropLast_cons_cons]
            simp only [TTree.nodes, Finset.mem_insert, Finset.mem_union, cons_mem, reduceCtorEq,
              false_or]
            rcases h with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩
            · exact Or.inl (Or.inl ⟨rfl, by simpa using ihl _ h⟩)
            · exact Or.inl (Or.inr ⟨rfl, by simpa using ihm _ h⟩)
            · exact Or.inr ⟨rfl, by simpa using ihr _ h⟩
    exact key _ _ a.2⟩

end LayeredGarden
end WaveTurbulence
