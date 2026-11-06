/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBRedirectEdges
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CollapseIncomingPayload
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.PairedTreeLeafGraph
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.StretchRange

/-! # Exact B-mini graph-contraction comparison at every surviving leaf -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem miniB_contract_leaf {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {b c : GBranch G.garden.tree} {k : MiniTreeCode} (h : MiniBOccurrence G.garden b c k)
    (hG : G.garden.IsPlain) (ℓ : GLeaf (collapsePairedTreeGarden (h.isSubPairedTree hG)).tree) :
    let S := G.collapsePairedTree (h.isSubPairedTree hG)
    (G.graphDipole_of_branch hG h.branchDipole).contract (S.incoming ℓ.toNode) =
      S.graph.mate (S.incoming ℓ.toNode) := by
  let hs := h.isSubPairedTree hG
  let S := G.collapsePairedTree hs
  let D := G.graphDipole_of_branch hG h.branchDipole
  let r := G.incoming (pairedTreeLeafEmbedding hs ℓ).toNode
  have hi : S.incoming ℓ.toNode = redirect (G.incoming (c.child k.lone)) (G.incoming b.toNode) r :=
    G.collapsePairedTree_incoming_redirect hs ℓ.toNode
  have hrx : r ≠ G.incoming b.toNode := fun he => h.node_embedding_ne_upper hG ℓ.toNode (G.incoming_injective he)
  have hr : redirect (G.incoming (c.child k.lone)) (G.incoming b.toNode) r ∈ Set.range S.portEmbedding :=
    hi ▸ S.incoming_mem_range ℓ.toNode
  exact (congrArg D.contract hi).trans
    ((G.miniB_contract_redirect h hG r (G.incoming_ne_parent _ (G.label b)) hrx hr).trans
      (G.collapsePairedTree_graph_leaf hs ℓ).symm)

end WaveTurbulence.Reg.Skeleton.LabelledGarden
