/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Lemmas
/-! A zero-order forest has only its roots as nodes and no branching coordinates. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem leafForest_node_eq_root {w : ℕ} (tree : Fin w → TTree) (ht : ∀ j, tree j = TTree.leaf)
    (a : GNode tree) : a = GNode.root tree a.1.1 := by
  have hp := a.2
  rw [ht a.1.1, TTree.nodes, mem_singleton] at hp
  exact Subtype.ext (Prod.ext rfl hp)

theorem leafForest_no_branch {w : ℕ} (tree : Fin w → TTree) (ht : ∀ j, tree j = TTree.leaf) :
    IsEmpty (GBranch tree) := by
  refine ⟨fun b => ?_⟩
  have hb := b.2
  rw [ht b.1.1, TTree.branching] at hb
  exact notMem_empty _ hb

theorem leafForest_garden_order {w : ℕ} (G : Garden w) (ht : ∀ j, G.tree j = TTree.leaf) : G.order = 0 := by
  unfold Garden.order
  simp_rw [ht, TTree.order]
  exact sum_const_zero

end WaveTurbulence.Induct
