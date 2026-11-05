/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainEndpointGeometry
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CollapsePairing

/-! # Literal included chain pairs define an actual embedded paired-tree interval -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem subPairedTree_of_source_block {w : ℕ} (X : RegChain) (ζ : ℤˣ) (G : Garden w)
    (hG : G.IsPlain) (a b : GNode G.tree) (t : TTree)
    (ha : Comb.subtree (G.tree a.1.1) a.1.2 = some (X.plug ζ t))
    (hb : Comb.subtree (G.tree b.1.1) b.1.2 = some t)
    (hf : b.1 = addrExt a.1 X.lonePath)
    (hP : ∀ p ∈ X.pairsAt ζ a.1, p ∈ sourcePairs G) : Comb.IsSubPairedTree G a b := by
  have hcover (ℓ : GLeaf G.tree) :
      ℓ ∈ a.leavesBelow \ b.leavesBelow ↔ ℓ.1 ∈ pairEndpoints (X.pairsAt ζ a.1) := by
    have haℓ := leafAddresses_subtree_iff a (X.plug ζ t) ha ℓ
    have hbℓ := leafAddresses_subtree_iff b t hb ℓ
    rw [chain_leafAddresses] at haℓ
    rw [hf] at hbℓ
    constructor
    · intro h
      have hu := haℓ.mpr (Finset.mem_sdiff.mp h).1
      rcases Finset.mem_union.mp hu with hp | hp
      · exact hp
      · exact ((Finset.mem_sdiff.mp h).2 (hbℓ.mp hp)).elim
    · intro h
      apply Finset.mem_sdiff.mpr
      refine ⟨haℓ.mp (Finset.mem_union_left _ h),?_⟩
      intro hl
      have hd := (leafBelow_iff_below b ℓ).mp hl
      rw [hf] at hd
      exact chain_endpoint_not_below_lone X ζ a.1 ℓ.1 h hd
  constructor
  · change a.1.1 = b.1.1 ∧ a.1.2 <+: b.1.2
    rw [hf]
    exact ⟨rfl,List.prefix_append _ _⟩
  · intro ℓ hℓ
    exact ⟨Comb.pair_ne_of_plain hG ℓ,
      (hcover (G.pair ℓ)).mpr (pairEndpoints_source_partner_mem G _ hP ℓ ((hcover ℓ).mp hℓ))⟩

end WaveTurbulence.Reg.Skeleton
