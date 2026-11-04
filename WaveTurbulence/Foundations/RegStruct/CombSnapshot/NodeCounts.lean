/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Structure

/-! # Total node and forest counts (TARGET L628–L632) -/

public section

namespace WaveTurbulence.Comb
open TTree Finset

/-- A tree of order n has exactly 3n+1 nodes (TARGET L628). -/
theorem card_nodes (t : TTree) : t.nodes.card = 3 * t.order + 1 := by
  have he : t.nodes = t.leaves ∪ t.branching := by
    ext p
    simpa only [Finset.mem_union] using TreePath.mem_nodes_iff t p
  have hd : Disjoint t.leaves t.branching := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact TreePath.not_mem_branching_of_mem_leaves t hp hq
  rw [he, Finset.card_union_of_disjoint hd, card_leaves, card_branching]
  omega

/-- Count any family of forest addresses by summing over the tree indices. -/
theorem card_forestSet {w : ℕ} (tree : Fin w → TTree) (f : TTree → Finset Path) :
    (forestSet tree f).card = ∑ j, (f (tree j)).card := by
  rw [forestSet, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro j _
    exact Finset.card_image_of_injective _ (Prod.mk_right_injective j)
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, _, h⟩ := Finset.mem_image.mp hb
    exact hij (congrArg Prod.fst h).symm

/-- The leaf count of a width-w forest is 2n+w (TARGET L632). -/
theorem card_gleaf {w : ℕ} (tree : Fin w → TTree) :
    Fintype.card (GLeaf tree) = 2 * (∑ j, (tree j).order) + w := by
  have hc : Fintype.card (GLeaf tree) = (forestSet tree TTree.leaves).card :=
    @Fintype.card_of_subtype (Fin w × Path) (fun a => a.2 ∈ (tree a.1).leaves)
      (forestSet tree TTree.leaves) (fun _ => mem_forestSet tree)
      (inferInstanceAs (Fintype (GLeaf tree)))
  rw [hc, card_forestSet]
  simp only [card_leaves, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- The total node count of a width-w forest is 3n+w. -/
theorem card_gnode {w : ℕ} (tree : Fin w → TTree) :
    Fintype.card (GNode tree) = 3 * (∑ j, (tree j).order) + w := by
  have hc : Fintype.card (GNode tree) = (forestSet tree TTree.nodes).card :=
    @Fintype.card_of_subtype (Fin w × Path) (fun a => a.2 ∈ (tree a.1).nodes)
      (forestSet tree TTree.nodes) (fun _ => mem_forestSet tree)
      (inferInstanceAs (Fintype (GNode tree)))
  rw [hc, card_forestSet]
  simp only [card_nodes, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

end WaveTurbulence.Comb
