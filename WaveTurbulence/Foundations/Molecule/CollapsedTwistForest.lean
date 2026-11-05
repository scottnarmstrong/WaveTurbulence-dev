/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.InsertionBranchPieces

/-! # The common collapsed forest of the two unit-twist placements

TARGET twist: remove the actual lower crown, replacing it by a leaf.
Both placements then consist of inserting that crown at a distinguished
leaf of this common forest. The old forest is recovered by exact equality.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Replacing twice at the same address keeps only the second replacement. -/
theorem replaceAt_replaceAt : ∀ (t : TTree) (p : Path) (s r : TTree),
    Comb.replaceAt (Comb.replaceAt t p s) p r = Comb.replaceAt t p r
  | t, [], s, r => by simp [Comb.replaceAt]
  | .leaf, i::p, s, r => rfl
  | .node l m r₀, i::p, s, r => by
    fin_cases i <;> simp [Comb.replaceAt,replaceAt_replaceAt]

variable {w : ℕ} (G : Garden w) (b : GBranch G.tree)

/-- The literal lower rooted subtree. -/
@[expose] noncomputable def lowerCrown : TTree := Mole.spliceNodeSubtree G b.toNode

/-- The common forest obtained by collapsing the lower subtree. -/
@[expose] def commonForest : Fin w → TTree :=
  Function.update G.tree b.1.1 (Comb.collapseAt (G.tree b.1.1) b.1.2)

/-- The removed lower root is an actual leaf of the common forest. -/
@[expose] def collapsedRoot : GLeaf (commonForest G b) := ⟨b.1,by
  change b.1.2 ∈ (Function.update G.tree b.1.1 _ b.1.1).leaves
  rw [Function.update_self]
  exact Comb.mem_leaves_collapseAt (Mole.spliceNodeSubtree_spec G b.toNode)⟩

/-- Insert the removed crown back to recover exactly the original forest. -/
theorem restore_commonForest : insertLeaf (commonForest G b) (collapsedRoot G b) (lowerCrown G b) = G.tree := by
  funext j
  by_cases hj : j = b.1.1
  · subst j
    simp only [insertLeaf,collapsedRoot,Function.update_self]
    rw [commonForest,Function.update_self]
    change Comb.replaceAt (Comb.collapseAt (G.tree b.1.1) b.1.2) b.1.2 (lowerCrown G b) = G.tree b.1.1
    rw [Comb.collapseAt,replaceAt_replaceAt]
    exact Comb.replaceAt_self (Mole.spliceNodeSubtree_spec G b.toNode)
  · rw [insertLeaf_other _ _ _ j (by simpa only [collapsedRoot] using hj)]
    exact Function.update_of_ne hj _ _

/-- Any old leaf outside the lower subtree survives at exactly its old address. -/
@[expose] def commonOutsideLeaf (l : GLeaf G.tree) (hout : ¬ b.toNode.IsDesc l.toNode) :
    GLeaf (commonForest G b) := ⟨l.1,by
  by_cases hi : l.1.1 = b.1.1
  · change l.1.2 ∈ (Function.update G.tree b.1.1 _ l.1.1).leaves
    rw [hi,Function.update_self]
    apply (Comb.mem_leaves_collapseAt_iff (Mole.spliceNodeSubtree_spec G b.toNode)).mpr
    exact Or.inl ⟨hi ▸ l.2,fun hp => hout ⟨hi.symm,hp⟩⟩
  · rw [show commonForest G b l.1.1 = G.tree l.1.1 from Function.update_of_ne hi _ _]
    exact l.2⟩

end WaveTurbulence.Twist
