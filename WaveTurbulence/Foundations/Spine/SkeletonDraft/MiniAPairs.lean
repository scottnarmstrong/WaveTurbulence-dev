/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniCoupleEmbedding
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PairPartition

/-! # Exact canonical oriented pairs in an A mini -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree
namespace MiniAOccurrence

/-- Each internal mini edge can be read from the first corolla. -/
theorem removed_image_left {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {k : MiniCplCode}
    (h : MiniAOccurrence G b c k) (hG : G.IsPlain) :
    (b.toNode.leavesBelow ∪ c.toNode.leavesBelow).image (sourcePairAt G) =
      b.toNode.leavesBelow.image (sourcePairAt G) := by
  classical
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hp
    rcases Finset.mem_union.mp hℓ with hb | hc
    · exact Finset.mem_image.mpr ⟨ℓ,hb,rfl⟩
    · exact Finset.mem_image.mpr ⟨G.pair ℓ,h.flip.partner_below ℓ hc,sourcePairAt_pair G hG ℓ⟩
  · exact Finset.image_subset_image (Finset.subset_union_left)

/-- Exact finite table of the three new source A edges for a positive first root. -/
theorem removed_pairs {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {k : MiniCplCode}
    (h : MiniAOccurrence G b c k) (hG : G.IsPlain) (hb : nodeSign G.sig b.1 = 1) :
    (b.toNode.leavesBelow ∪ c.toNode.leavesBelow).image (sourcePairAt G) =
      {(addrExt b.1 [0],addrExt c.1 [k.partner 0]),
       (addrExt c.1 [1],addrExt b.1 [1]),
       (addrExt b.1 [2],addrExt c.1 [k.partner 2])} := by
  classical
  rw [h.removed_image_left hG]
  have hi : b.toNode.leavesBelow.image (sourcePairAt G) =
      Finset.univ.image (fun i : Fin 3 => orient (addrExt b.1 [i]) (slotSign (1 : ℤˣ) i)
        (addrExt c.1 [k.partner i])) := by
    ext p
    constructor
    · intro hp
      obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨i,hi⟩ := leaf_below_corolla G.tree b h.left_tree ℓ hℓ
      obtain ⟨x,y,hx,hy,hpair⟩ := h.2 i
      have he : ℓ = x := Subtype.ext (congrArg (fun a : GNode G.tree => a.1) (hi.trans hx.symm))
      subst ℓ
      refine Finset.mem_image.mpr ⟨i,Finset.mem_univ _,?_⟩
      rw [sourcePairAt_eq_orient,hpair]
      have hv := congrArg (fun a : GNode G.tree => a.1) hx
      have hw := congrArg (fun a : GNode G.tree => a.1) hy
      change x.1 = addrExt b.1 [i] at hv
      change y.1 = addrExt c.1 [k.partner i] at hw
      rw [hv,hw,nodeSign_step,hb]
    · intro hp
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨x,y,hx,hy,hpair⟩ := h.2 i
      refine Finset.mem_image.mpr ⟨x,child_leaf_below G.tree b i x hx,?_⟩
      rw [sourcePairAt_eq_orient,hpair]
      have hv := congrArg (fun a : GNode G.tree => a.1) hx
      have hw := congrArg (fun a : GNode G.tree => a.1) hy
      change x.1 = addrExt b.1 [i] at hv
      change y.1 = addrExt c.1 [k.partner i] at hw
      rw [hv,hw,nodeSign_step,hb]
  rw [hi]
  fin_cases k <;> simp [Fin.univ_succ,orient,slotSign,MiniCplCode.partner]

end MiniAOccurrence
end WaveTurbulence.Reg.Skeleton
