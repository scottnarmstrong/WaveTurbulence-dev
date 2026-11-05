/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerEmbeddings
/-! The original top nodes embed into the graft; top leaves are the lower roots. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def topNodeEmbedding {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    GNode top ↪ GNode (graftForest top (blockGraftTrees top P low)) where
  toFun a := ⟨a.1, by
    apply (mem_nodes_graftTree (top a.1.1) (blockGraftTrees top P low a.1.1) a.1.2).mpr
    rcases (TTree.mem_nodes_iff _ _).mp a.2 with hl | hb
    · exact Or.inr ⟨a.1.2, hl, [], TTree.nil_mem_nodes _, List.append_nil _⟩
    · exact Or.inl hb⟩
  inj' _ _ h := Subtype.ext (congrArg
    (fun z : GNode (graftForest top (blockGraftTrees top P low)) => z.1) h)

theorem topNodeEmbedding_branch {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (a : GBranch top) :
    topNodeEmbedding top P low a.toNode = gardenNodeEquiv top P low (.inl a) := by
  apply Subtype.ext
  exact (gardenNodeEquiv_top_val top P low a).symm

theorem topNodeEmbedding_leaf {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (a : GLeaf top) :
    topNodeEmbedding top P low a.toNode =
      lowerNodeEmbedding top P low (blockRootEquiv top P a).1
        (GNode.root (low (blockRootEquiv top P a).1).tree (blockRootEquiv top P a).2) := by
  apply Subtype.ext
  have hv := gardenNodeEquiv_lower_val top P low (blockRootEquiv top P a).1
    (GNode.root (low (blockRootEquiv top P a).1).tree (blockRootEquiv top P a).2)
  have he := (blockRootEquiv top P).symm_apply_apply a
  have he' := congrArg (fun ℓ : GLeaf top => (ℓ.1.1, ℓ.1.2 ++ ([] : TTree.Path))) he
  exact (hv.trans (he'.trans (by simp only [List.append_nil]; rfl))).symm

theorem topNodeEmbedding_lower_root {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (k : Fin B.1.card) :
    topNodeEmbedding top P low ((blockRootEquiv top P).symm ⟨B, k⟩).toNode =
      lowerNodeEmbedding top P low B (GNode.root (low B).tree k) := by
  apply Subtype.ext
  have hv := gardenNodeEquiv_lower_val top P low B (GNode.root (low B).tree k)
  exact (hv.trans (by simp only [GNode.root, List.append_nil]; rfl)).symm

theorem topBranch_child {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (b : GBranch top) (i : Fin 3) :
    (gardenBranchEquiv top P low (.inl b)).child i = topNodeEmbedding top P low (b.child i) := by
  apply Subtype.ext
  have hv := gardenBranchEquiv_top_val top P low b
  exact congrArg (fun z : Fin w × TTree.Path => (z.1, z.2 ++ [i])) hv

end WaveTurbulence.Induct
