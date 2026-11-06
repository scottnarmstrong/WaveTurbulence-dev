/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniPairedTreeEmbedding
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PairPartition

/-! # The removed B-mini pairs are precisely the literal two side pairs -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree
namespace MiniBOccurrence

/-- An actual upper side leaf and its actual lower partner give the literal framed pair. -/
theorem side_pair {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (i j : Fin 3) (ℓ q : GLeaf G.tree)
    (hℓ : ℓ.toNode = b.child i) (hq : q.toNode = c.child j) (hp : G.pair ℓ = q) :
    sourcePairAt G ℓ = orient (addrExt b.1 [i]) (slotSign (nodeSign G.sig b.1) i)
      (addrExt b.1 [m.c,j]) := by
  have hl : ℓ.1 = addrExt b.1 [i] := congrArg (fun a : GNode G.tree => a.1) hℓ
  have hq' : q.1 = addrExt b.1 [m.c,j] :=
    (congrArg (fun a : GNode G.tree => a.1) hq).trans (h.lower_frame j)
  rw [sourcePairAt_eq_orient,hp,hl,hq']
  congr 1
  exact nodeSign_step G.sig b.1 i

/-- The canonical pairs of the removed interval are exactly the two source mini pairs. -/
theorem removed_pairs {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {m : MiniTreeCode}
    (h : MiniBOccurrence G b c m) (hG : G.IsPlain) :
    (b.toNode.leavesBelow \ (c.child m.lone).leavesBelow).image (sourcePairAt G) =
      miniPairs G.sig b.1 m := by
  classical
  obtain ⟨ℓr,qr,hℓr,hqr,hpr⟩ := h.2.1
  obtain ⟨ℓg,qg,hℓg,hqg,hpg⟩ := h.2.2
  rw [h.interval_eq_four ℓr qr ℓg qg hℓr hqr hℓg hqg]
  have hr := h.side_pair _ _ ℓr qr hℓr hqr hpr
  have hg := h.side_pair _ _ ℓg qg hℓg hqg hpg
  have hqr' : sourcePairAt G qr = sourcePairAt G ℓr := by
    rw [← hpr]; exact sourcePairAt_pair G hG ℓr
  have hqg' : sourcePairAt G qg = sourcePairAt G ℓg := by
    rw [← hpg]; exact sourcePairAt_pair G hG ℓg
  simp only [Finset.image_insert,Finset.image_singleton,hqr',hqg',hr,hg]
  ext p
  simp [miniPairs,or_assoc]

end MiniBOccurrence
end WaveTurbulence.Reg.Skeleton
