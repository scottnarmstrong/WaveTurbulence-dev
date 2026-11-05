/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LeafForest
/-! The leaf carrier of a zero-order forest is exactly its ordered root set. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def leafRoot {w : ℕ} (tree : Fin w → TTree) (ht : ∀ j, tree j = TTree.leaf)
    (j : Fin w) : GLeaf tree := ⟨(j, []), by rw [ht j]; exact mem_singleton_self []⟩

noncomputable def leafForestLeafEquiv {w : ℕ} (tree : Fin w → TTree) (ht : ∀ j, tree j = TTree.leaf) :
    GLeaf tree ≃ Fin w where
  toFun l := l.1.1
  invFun j := leafRoot tree ht j
  left_inv l := by
    have he := leafForest_node_eq_root tree ht l.toNode
    exact Subtype.ext (congrArg (fun a : GNode tree => a.1) he).symm
  right_inv _ := rfl

theorem leafForest_sign {w : ℕ} (G : Garden w) (ht : ∀ j, G.tree j = TTree.leaf)
    (l : GLeaf G.tree) : G.sign l.toNode = G.sig l.1.1 := by
  have he := leafForest_node_eq_root G.tree ht l.toNode
  exact (congrArg G.sign he).trans (by
    simp only [Garden.sign, nodeSign, GNode.root, TTree.pathSign, List.count_nil, pow_zero, mul_one]
    rfl)

end WaveTurbulence.Induct
