/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PairMembership
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.InducedGarden

/-! # Exact branch and ordered-child embeddings of actual rooted source subforests -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

def subforestBranchEmbedding {w v : ℕ} {tree : Fin w → TTree} (E : Comb.RootedSubforest tree v) :
    GBranch E.shape ↪ GBranch tree where
  toFun b := ⟨((E.root b.1.1).1.1,(E.root b.1.1).1.2 ++ b.1.2),
    (Comb.subtree_branching_iff (E.subtree_eq b.1.1) b.1.2).mp b.2⟩
  inj' := by
    intro a b he
    have hn : E.nodeEmbedding a.toNode = E.nodeEmbedding b.toNode :=
      Subtype.ext (congrArg (fun z : GBranch tree => z.1) he)
    exact Subtype.ext (congrArg (fun z : GNode E.shape => z.1) (E.nodeEmbedding.injective hn))

theorem subforest_node_root {w v : ℕ} {tree : Fin w → TTree} (E : Comb.RootedSubforest tree v)
    (j : Fin v) : E.nodeEmbedding (GNode.root E.shape j) = E.root j := by
  apply Subtype.ext
  exact Prod.ext rfl (List.append_nil _)

theorem subforest_node_child {w v : ℕ} {tree : Fin w → TTree} (E : Comb.RootedSubforest tree v)
    (b : GBranch E.shape) (i : Fin 3) :
    E.nodeEmbedding (b.child i) = (subforestBranchEmbedding E b).child i := by
  apply Subtype.ext
  change ((E.root b.1.1).1.1,(E.root b.1.1).1.2 ++ (b.1.2 ++ [i])) =
    ((E.root b.1.1).1.1,((E.root b.1.1).1.2 ++ b.1.2) ++ [i])
  exact Prod.ext rfl (List.append_assoc _ _ _).symm

theorem subforest_node_sign {w v : ℕ} {tree : Fin w → TTree} (E : Comb.RootedSubforest tree v)
    (σ : Fin w → ℤˣ) (a : GNode E.shape) :
    nodeSign (Comb.RootedSubforest.signature E σ) a.1 = nodeSign σ (E.nodeEmbedding a).1 := by
  change pathSign (pathSign (σ (E.root a.1.1).1.1) (E.root a.1.1).1.2) a.1.2 =
    pathSign (σ (E.root a.1.1).1.1) ((E.root a.1.1).1.2 ++ a.1.2)
  exact (Comb.pathSign_append _ _ _).symm

end WaveTurbulence.Reg.Skeleton
