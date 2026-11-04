/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeTimeOrder
public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # Exact branch-clock support when a source couple tree is trivial -/

public section
namespace WaveTurbulence.IncohInst

/-- A source tree whose root is not branching is the single-leaf tree. -/
theorem tree_eq_leaf_of_root_not_branching {t : TTree} (h : ([] : TTree.Path) ∉ t.branching) :
    t = .leaf := by
  cases t with
  | leaf => rfl
  | node l m r => exact False.elim (h (by simp [TTree.branching]))

/-- If the other source tree is trivial, every actual branching clock lies in the active tree. -/
theorem branch_index_eq_of_other_leaf (G : Garden 2) (a : Fin 2)
    (h : ∀ i, i ≠ a → G.tree i = .leaf) :
    ∀ b : GBranch G.tree, b.1.1 = a := by
  intro b
  by_contra hb
  have hm := b.2
  rw [h b.1.1 hb, TTree.branching] at hm
  exact Finset.notMem_empty _ hm

end WaveTurbulence.IncohInst
