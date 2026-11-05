/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BlockGraft
public import WaveTurbulence.Foundations.XChain.TreeCut
/-! Recovery of every attached tree from its literal top-leaf address. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem graftForest_lower_subtree {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (k : Fin B.1.card) :
    subtreeAt (graftForest top (blockGraftTrees top P low)
      ((blockRootEquiv top P).symm ⟨B, k⟩).1.1)
      ((blockRootEquiv top P).symm ⟨B, k⟩).1.2 = (low B).tree k := by
  let a := (blockRootEquiv top P).symm ⟨B, k⟩
  have ht := subtreeAt_graftTree_leaf (top a.1.1) (blockGraftTrees top P low a.1.1) a.2
  have hb := blockGraftTrees_at_leaf top P low a
  have he := congrArg (fun z : Σ B : P.parts, Fin B.1.card => (low z.1).tree z.2)
    ((blockRootEquiv top P).apply_symm_apply ⟨B, k⟩)
  exact ht.trans (hb.trans he)

theorem graftForest_injective_lower_trees {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    (low high : (B : P.parts) → Garden B.1.card)
    (he : graftForest top (blockGraftTrees top P low) = graftForest top (blockGraftTrees top P high))
    (B : P.parts) (k : Fin B.1.card) : (low B).tree k = (high B).tree k := by
  have ht := congrArg (fun tree : Fin w → TTree =>
    subtreeAt (tree ((blockRootEquiv top P).symm ⟨B, k⟩).1.1)
      ((blockRootEquiv top P).symm ⟨B, k⟩).1.2) he
  exact (graftForest_lower_subtree top P low B k).symm.trans
    (ht.trans (graftForest_lower_subtree top P high B k))

end WaveTurbulence.Induct
