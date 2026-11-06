/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.EmbeddedChainShape
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.EmbeddedPairedTreeMarks
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ChainPairRecovery

/-! # Exact C1 decoding of an actual embedded chain interval -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem embeddedPairedTree_decodes_of_block {w : ℕ} (X : RegChain) (G : Garden w)
    (a b : GNode G.tree) (hc : Comb.IsSubPairedTree G a b) (t : TTree)
    (ha : Comb.subtree (G.tree a.1.1) a.1.2 = some (X.plug (G.sign a) t))
    (hf : b.1 = addrExt a.1 X.lonePath)
    (hP : ∀ p ∈ X.pairsAt (G.sign a) a.1, p ∈ sourcePairs G) :
    X.DecodesTree (Comb.embeddedPairedTree hc) := by
  let D := Comb.collapseDataOfDesc hc.1
  let H := Comb.embeddedPairedTree hc
  have hp : D.path = X.lonePath := by
    apply List.append_cancel_left (as := a.1.2)
    exact D.path_eq.trans (congrArg (fun z : Address w => z.2) hf)
  have ht := embeddedPairedTree_shape_of_chain X (G.sign a) G a b hc t ha hf
  refine ⟨ht,?_,?_⟩
  · intro ℓ
    exact (embeddedPairedTree_mark hc ℓ).trans (by rw [show (Comb.collapseDataOfDesc hc.1).path = X.lonePath from hp])
  · intro ℓ hn
    let x : D.OtherLeaf := ⟨ℓ,by
      intro he
      have heP := congrArg (fun z : GLeaf H.tree => z.1.2) he
      exact hn (heP.trans hp)⟩
    obtain ⟨y,hy,hyP⟩ := embeddedPairedTree_pair_transport hc x
    apply chain_pair_mem_of_ambient X (G.sign a) G a.1 ℓ.1 (H.pair ℓ).1
      (Comb.CollapseData.leafEmbedding D x) (Comb.CollapseData.leafEmbedding D y)
    · have hleaf := ℓ.2
      have hi : ℓ.1.1 = 0 := Subsingleton.elim _ _
      change ℓ.1.2 ∈ (H.tree ℓ.1.1).leaves at hleaf
      rw [hi,ht] at hleaf
      exact hleaf
    · exact hn
    · rfl
    · exact congrArg (fun z : GLeaf H.tree => addrExt a.1 z.1.2) hy.symm
    · exact hyP.symm
    · exact hP

end WaveTurbulence.Reg.Skeleton
