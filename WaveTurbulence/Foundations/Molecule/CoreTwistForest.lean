/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CorePlacements
public import WaveTurbulence.Foundations.Molecule.TwistLeafSigns

/-! # The concrete ordered forest of a unit twist

TARGET Definition twist: exchange the actual lower crown with u0, keep
the u23 child slot, and switch the other two subtrees. Pairing transport
is constructed separately from the concrete leaf bijection.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Change only the proof of leaf membership when two forests are equal. -/
@[expose] def forestLeafCast {w : ℕ} {F H : Fin w → TTree} (he : F = H) : GLeaf F ≃ GLeaf H where
  toFun l := ⟨l.1,by simpa only [← he] using l.2⟩
  invFun l := ⟨l.1,by simpa only [he] using l.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Change only the proof of branch membership when two forests are equal. -/
@[expose] def forestBranchCast {w : ℕ} {F H : Fin w → TTree} (he : F = H) : GBranch F ≃ GBranch H where
  toFun b := ⟨b.1,by simpa only [← he] using b.2⟩
  invFun b := ⟨b.1,by simpa only [he] using b.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- The actual leaf u0 in the common collapsed forest. -/
@[expose] def pairedHole : GLeaf (commonForest G P.lower) :=
  commonOutsideLeaf G P.lower (G.pair P.retained) P.paired_outside

/-- The actual ordered forest after the unit twist. -/
@[expose] noncomputable def coreTwistForest : Fin w → TTree :=
  insertLeaf (commonForest G P.lower) (pairedHole G P)
    (switchFree P.keep (lowerCrown G P.lower))

/-- Actual leaf bijection from the original garden to its concrete twisted forest. -/
@[expose] noncomputable def coreLeafEquiv : GLeaf G.tree ≃ GLeaf (coreTwistForest G P) :=
  (forestLeafCast (restore_commonForest G P.lower).symm).trans
    (exchangeLeafEquiv (commonForest G P.lower) (collapsedRoot G P.lower) (pairedHole G P)
      P.keep (lowerCrown G P.lower))

/-- Actual branching-node bijection for the same concrete twist. -/
@[expose] noncomputable def coreBranchEquiv : GBranch G.tree ≃ GBranch (coreTwistForest G P) :=
  (forestBranchCast (restore_commonForest G P.lower).symm).trans
    (exchangeBranchEquiv (commonForest G P.lower) (collapsedRoot G P.lower)
      (lowerCrown G P.lower) (pairedHole G P) P.keep)

/-- The retained lower child is literally a leaf subtree of the extracted crown. -/
theorem lowerCrown_retained_leaf : Comb.subtree (lowerCrown G P.lower) [P.keep] = some .leaf := by
  have hlidx := congrArg (fun n : GNode G.tree => n.1.1) P.child
  have hlpath := congrArg (fun n : GNode G.tree => n.1.2) P.child
  change P.retained.1.1 = P.lower.1.1 at hlidx
  change P.retained.1.2 = P.lower.1.2 ++ [P.keep] at hlpath
  have hs : Comb.subtree (G.tree P.lower.1.1) (P.lower.1.2 ++ [P.keep]) = some .leaf := by
    rw [← hlpath]
    apply (subtree_leaf_iff _ _).mpr
    exact hlidx ▸ P.retained.2
  have he : Comb.subtree (G.tree P.lower.1.1) P.lower.1.2 = some (lowerCrown G P.lower) :=
    Mole.spliceNodeSubtree_spec G P.lower.toNode
  rw [Comb.subtree_append,he] at hs
  exact hs

/-- The lower crown root is a branch, hence not a leaf. -/
theorem lowerCrown_root_not_leaf : [] ∉ (lowerCrown G P.lower).leaves := by
  have hb : [] ∈ (lowerCrown G P.lower).branching :=
    (Comb.subtree_branching_iff (Mole.spliceNodeSubtree_spec G P.lower.toNode) []).mpr (by
      simpa only [List.append_nil,GBranch.toNode] using P.lower.2)
  exact fun hl => TTree.not_mem_branching_of_mem_leaves _ hl hb

end WaveTurbulence.Twist
