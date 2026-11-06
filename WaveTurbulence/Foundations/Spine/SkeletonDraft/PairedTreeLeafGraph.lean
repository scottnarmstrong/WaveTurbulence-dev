/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CollapseIncomingRedirect

/-! # Graph edges at source leaves under paired-tree incoming-slot redirection -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem collapsePairedTree_graph_leaf {w : ℕ} {B : Type*} [DecidableEq B] (G : LabelledGarden w B)
    {a b : GNode G.garden.tree} (h : Comb.IsSubPairedTree G.garden a b)
    (ℓ : GLeaf (collapsePairedTreeGarden h).tree) :
    (G.collapsePairedTree h).graph.mate ((G.collapsePairedTree h).incoming ℓ.toNode) =
      redirect (G.incoming b) (G.incoming a)
        (G.graph.mate (G.incoming (pairedTreeLeafEmbedding h ℓ).toNode)) := by
  let S := G.collapsePairedTree h
  have hp : collapsePairedTreeNodeEmbedding h ((collapsePairedTreeGarden h).pair ℓ).toNode =
      (G.garden.pair (pairedTreeLeafEmbedding h ℓ)).toNode :=
    congrArg (fun q : GLeaf G.garden.tree => q.toNode) (collapsePairedTreeGarden_pair h ℓ)
  calc
    S.graph.mate (S.incoming ℓ.toNode) = S.incoming ((collapsePairedTreeGarden h).pair ℓ).toNode :=
      S.graph_mate_incoming_leaf ℓ
    _ = redirect (G.incoming b) (G.incoming a)
        (G.incoming (collapsePairedTreeNodeEmbedding h ((collapsePairedTreeGarden h).pair ℓ).toNode)) :=
      G.collapsePairedTree_incoming_redirect h _
    _ = redirect (G.incoming b) (G.incoming a)
        (G.incoming (G.garden.pair (pairedTreeLeafEmbedding h ℓ)).toNode) := by rw [hp]
    _ = redirect (G.incoming b) (G.incoming a)
        (G.graph.mate (G.incoming (pairedTreeLeafEmbedding h ℓ).toNode)) :=
      congrArg (redirect (G.incoming b) (G.incoming a)) (G.graph_mate_incoming_leaf _).symm

end WaveTurbulence.Reg.Skeleton.LabelledGarden
