/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapseBranchLabels
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.IncomingTransport

/-! # Every surviving couple-collapse node retains its original incoming slot -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Every actual node after two-root collapse is an actual original node at the same address. -/
theorem collapsePairForest_node_subset {w : ℕ} (tree : Fin w → TTree) (a b : GNode tree)
    (hab : a.Incomparable b) (x : GNode (collapsePairForest tree a b hab)) :
    x.1.2 ∈ (tree x.1.1).nodes := by
  rcases (Comb.TreePath.mem_nodes_iff _ _).mp x.2 with hl | hb
  · rcases (collapsePairForest_leaf_iff tree a b hab x.1).mp hl with ⟨hl,_,_⟩ | he | he
    · exact (Comb.TreePath.mem_nodes_iff _ _).mpr (Or.inl hl)
    · rw [he]
      exact a.2
    · rw [he]
      exact b.2
  · exact (Comb.TreePath.mem_nodes_iff _ _).mpr
      (Or.inr ((collapsePairForest_branch_iff tree a b hab x.1).mp hb).1)

/-- Exact address-preserving node embedding induced by actual couple collapse. -/
def collapseCoupleNodeEmbedding {w : ℕ} {G : Garden w} {a b : GNode G.tree}
    (h : Comb.IsSubCouple G a b) : GNode (collapseCoupleGarden h).tree ↪ GNode G.tree where
  toFun x := ⟨x.1,collapsePairForest_node_subset G.tree a b (Comb.subCouple_incomparable h) x⟩
  inj' := fun _x _y he => Subtype.ext (congrArg (fun z : GNode G.tree => z.1) he)

/-- Incoming ports of all surviving actual source nodes retain their literal original identity. -/
theorem LabelledGarden.collapseCouple_incoming {w : ℕ} {B : Type*} (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubCouple G.garden a b)
    (x : GNode (collapseCoupleGarden h).tree) :
    (G.collapseCouple h).incoming x = G.incoming (collapseCoupleNodeEmbedding h x) := by
  exact (G.collapseCouple h).incoming_eq_of_branch_embedding G
    (collapseCoupleBranchEmbedding h) (fun _ => rfl) (fun _ => rfl) x _ rfl

end WaveTurbulence.Reg.Skeleton
