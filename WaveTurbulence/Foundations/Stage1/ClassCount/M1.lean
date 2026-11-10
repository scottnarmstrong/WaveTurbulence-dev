/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.Labelling
public import WaveTurbulence.Foundations.Stage1.ClassCount.ArcCode
public import WaveTurbulence.Foundations.Stage1.ClassCount.Arcs
import Mathlib.Tactic

/-!
# CLASSCOUNT (M1): the arc multiset of a garden with disjoint ladders

For a garden `G` whose molecule has a family of pairwise disjoint ladders `F`, there is a labelling
`ℓ : GBranch G.tree ≃ Fin (nn G)` and a list `L ∈ arcLists n K {0}`, `K = 4 (#free atoms + #ladders)`, whose arc counts
are those of the bonds of `G` (`exists_garden_arcList`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Mole

namespace LadderFam
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {ι : Type}
  (F : LadderFam M ι)

theorem bb_le_two {a b : V} (h : F.Reg a b) : M.bondsBetween a b ≤ 2 := by
  obtain ⟨i, hreg⟩ := h
  rcases hreg with ⟨j, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨j, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact (bb_uv F i j).le
  · exact (bb_vu F i j).le
  · exact (bb_uu F i j.castSucc j.succ (by simp)).le.trans (by norm_num)
  · exact (bb_uu' F i j.succ j.castSucc (by simp)).le.trans (by norm_num)
  · exact (bb_vv F i j.castSucc j.succ (by simp)).le.trans (by norm_num)
  · exact (bb_vv' F i j.succ j.castSucc (by simp)).le.trans (by norm_num)

end LadderFam


end WaveTurbulence.ClassCount
