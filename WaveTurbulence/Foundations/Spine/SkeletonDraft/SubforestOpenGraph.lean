/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SubforestOpenMatching

/-! # Actual pairing-closed rooted subforests are open matching embeddings -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Internal branches keep their original ambient identities; source roots receive fresh dummy
vertex names (their actual active attachment ports remain the original ambient root slots). -/
noncomputable def subforestVertexEmbedding {w v : ℕ} (G : Garden w)
    (E : Comb.RootedSubforest G.tree v) (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) :
    Vertex (E.inducedGarden hc) ↪ Fin w ⊕ (GBranch G.tree ⊕ Fin v) :=
  ((Equiv.sumComm (Fin v) (GBranch E.shape)).toEmbedding.trans
    ((subforestBranchEmbedding E).sumMap (Function.Embedding.refl (Fin v)))).trans Function.Embedding.inr

/-- The actual source subforest, with genuine external attachment slots and all inactive padding,
embeds into the actual ambient garden matching. No matching-compatibility premise is assumed. -/
noncomputable def subforestOpenGraph {w v : ℕ} (G : Garden w) (E : Comb.RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (Comb.RootedSubforest.leafSet E)) :
    PortMatching.OpenEmbedding (selfLabelled (E.inducedGarden hc)).graph
      (ambientWithPadding (v := v) G).graph where
  port := subforestOpenPortEmbedding G E hc
  internal := Finset.univ.image (Sum.inr : GBranch E.shape → Vertex (E.inducedGarden hc))
  vertex := (Function.Embedding.subtype _).trans (subforestVertexEmbedding G E hc)
  port_vertex := by
    intro a i
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp a.2
    change subforestOpenPort G E hc (a.1,i) = (subforestVertexEmbedding G E hc a.1,i)
    rw [← he]
    exact subforestOpenPort_branch G E hc b i
  outside_fixed := by
    intro a ha
    cases a with
    | inl j => exact ⟨1,(selfLabelled (E.inducedGarden hc)).graph_root_inactive j 1 (by decide)⟩
    | inr b => exact (ha (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩)).elim
  mate := subforestOpenPort_mate G E hc

end WaveTurbulence.Reg.Skeleton
