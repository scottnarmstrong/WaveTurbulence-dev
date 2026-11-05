/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.GenericInflation
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionGarden

/-! # Exact raw lookup representation of the actual reconstruction operation

Outside the valid source carriers the lookups return nil/leaf. Those values
are never used at valid source branching/leaf nodes; they also make the two
common-forest holes literal leaves during the naturality argument.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton
variable {w : ℕ} {S : Garden w}

@[expose] noncomputable def branchLookup (D : ReconstructionData S) (a : Address w) : RegChain :=
  if h : a.2 ∈ (S.tree a.1).branching then D.tree ⟨a,h⟩ else .nil

@[expose] noncomputable def leafLookup (D : ReconstructionData S) (hS : S.IsPlain) (a : Address w) : TTree :=
  if h : a.2 ∈ (S.tree a.1).leaves then D.leafTree hS ⟨a,h⟩ else .leaf

theorem branchLookup_branch (D : ReconstructionData S) (b : GBranch S.tree) :
    branchLookup D b.1 = D.tree b := by
  rw [branchLookup, dite_eq_left b.2]
  rfl

theorem leafLookup_leaf (D : ReconstructionData S) (hS : S.IsPlain) (l : GLeaf S.tree) :
    leafLookup D hS l.1 = D.leafTree hS l := by
  rw [leafLookup, dite_eq_left l.2]
  rfl

theorem leafLookup_branch (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) :
    leafLookup D hS b.1 = .leaf := by
  apply dite_eq_right
  exact fun hl => Comb.TreePath.not_mem_branching_of_mem_leaves _ hl b.2

/-- The pre-existing actual reconstruction is precisely raw local tree inflation. -/
theorem inflateNode_eq_raw (D : ReconstructionData S) (hS : S.IsPlain) (a : GNode S.tree) :
    D.inflateNode hS a = inflateTreeAt S.sig (branchLookup D) (leafLookup D hS) (Comb.nodeSubtree a) a.1 := by
  rcases (TTree.mem_nodes_iff _ _).mp a.2 with hl | hb
  · let l : GLeaf S.tree := ⟨a.1,hl⟩
    have he : a = l.toNode := Subtype.ext rfl
    rw [he, D.inflateNode_leaf hS l, nodeSubtree_leaf S.tree l]
    exact (leafLookup_leaf D hS l).symm
  · let b : GBranch S.tree := ⟨a.1,hb⟩
    have he : a = b.toNode := Subtype.ext rfl
    rw [he, D.inflateNode_branch hS b, nodeSubtree_branch S.tree b]
    change (D.tree b).plug (nodeSign S.sig b.1)
      (.node (D.inflateNode hS (b.child 0)) (D.inflateNode hS (b.child 1)) (D.inflateNode hS (b.child 2))) =
      (branchLookup D b.1).plug (nodeSign S.sig b.1)
      (.node (inflateTreeAt S.sig (branchLookup D) (leafLookup D hS) (Comb.nodeSubtree (b.child 0)) (b.child 0).1)
        (inflateTreeAt S.sig (branchLookup D) (leafLookup D hS) (Comb.nodeSubtree (b.child 1)) (b.child 1).1)
        (inflateTreeAt S.sig (branchLookup D) (leafLookup D hS) (Comb.nodeSubtree (b.child 2)) (b.child 2).1))
    rw [branchLookup_branch]
    apply congrArg ((D.tree b).plug (nodeSign S.sig b.1))
    congr 1
    · exact inflateNode_eq_raw D hS (b.child 0)
    · exact inflateNode_eq_raw D hS (b.child 1)
    · exact inflateNode_eq_raw D hS (b.child 2)
termination_by (Comb.nodeSubtree a).order
decreasing_by all_goals exact nodeSubtree_child_order_lt S.tree _ _

/-- The actual full reconstruction forest is the raw inflation of its source forest. -/
theorem reconstruction_forest_eq_raw (D : ReconstructionData S) (hS : S.IsPlain) (j : Fin w) :
    D.forest hS j = inflateTreeAt S.sig (branchLookup D) (leafLookup D hS) (S.tree j) (j,[]) := by
  have hroot : Comb.nodeSubtree (GNode.root S.tree j) = S.tree j := by
    have hh := Comb.nodeSubtree_spec (GNode.root S.tree j)
    simp only [GNode.root, Comb.subtree] at hh
    exact (Option.some.inj hh).symm
  exact (inflateNode_eq_raw D hS (GNode.root S.tree j)).trans
    (congrArg (fun t => inflateTreeAt S.sig (branchLookup D) (leafLookup D hS) t (j,[])) hroot)

end WaveTurbulence.LFTwist
