/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SubforestBranches

/-! # Actual mini pieces inside an induced source subforest remain actual ambient mini pieces -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem subforest_branch_node {w v : ℕ} {tree : Fin w → TTree} (E : Comb.RootedSubforest tree v)
    (b : GBranch E.shape) : E.nodeEmbedding b.toNode = (subforestBranchEmbedding E b).toNode :=
  Subtype.ext rfl

theorem subforest_leaf_node {w v : ℕ} {tree : Fin w → TTree} (E : Comb.RootedSubforest tree v)
    (ℓ : GLeaf E.shape) : (E.leafEmbedding ℓ).toNode = E.nodeEmbedding ℓ.toNode := Subtype.ext rfl

theorem leafBond_subforest_lift {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E))
    {b c : GBranch E.shape} {i j : Fin 3} (h : LeafBond (E.inducedGarden hc) b c i j) :
    LeafBond G (subforestBranchEmbedding E b) (subforestBranchEmbedding E c) i j := by
  obtain ⟨ℓ,q,hℓ,hq,hp⟩ := h
  refine ⟨E.leafEmbedding ℓ,E.leafEmbedding q,?_,?_,?_⟩
  · exact (subforest_leaf_node E ℓ).trans
      ((congrArg E.nodeEmbedding hℓ).trans (subforest_node_child E b i))
  · exact (subforest_leaf_node E q).trans
      ((congrArg E.nodeEmbedding hq).trans (subforest_node_child E c j))
  · exact (E.inducedGarden_pair hc ℓ).symm.trans (congrArg E.leafEmbedding hp)

theorem miniA_subforest_lift {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E))
    {b c : GBranch E.shape} {k : MiniCplCode} (h : MiniAOccurrence (E.inducedGarden hc) b c k) :
    MiniAOccurrence G (subforestBranchEmbedding E b) (subforestBranchEmbedding E c) k := by
  have hb : (E.inducedGarden hc).sign b.toNode = G.sign (subforestBranchEmbedding E b).toNode :=
    subforest_node_sign E G.sig b.toNode
  have hc' : (E.inducedGarden hc).sign c.toNode = G.sign (subforestBranchEmbedding E c).toNode :=
    subforest_node_sign E G.sig c.toNode
  refine ⟨hc'.symm.trans (h.1.trans (congrArg Neg.neg hb)),?_⟩
  intro i
  exact leafBond_subforest_lift G E hc (h.2 i)

theorem miniB_subforest_lift {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E))
    {b c : GBranch E.shape} {k : MiniTreeCode} (h : MiniBOccurrence (E.inducedGarden hc) b c k) :
    MiniBOccurrence G (subforestBranchEmbedding E b) (subforestBranchEmbedding E c) k := by
  refine ⟨?_,leafBond_subforest_lift G E hc h.2.1,leafBond_subforest_lift G E hc h.2.2⟩
  exact (subforest_node_child E b k.c).symm.trans
    ((congrArg E.nodeEmbedding h.1).trans (subforest_branch_node E c))

end WaveTurbulence.Reg.Skeleton
