/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.PairTransfer
public import WaveTurbulence.Foundations.LayerCnt.HExit3
import Mathlib.Tactic

/-! # The canonical pair criterion on the erased region (TARGET Remark `sublayer`, region version)

`canonPairs_of_region`: for a canonical layered object `LG` decoding the skeleton `S`, the induced skeleton pre-layering
satisfies the pair criterion `CanonPairs` on every node of a region whose regular attachments are coherent:
erase them (`erase_region`), then transfer the criterion of the erased object to the skeleton nodes.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree Reg Reg.Skeleton Links LFTwist Twist
variable {w : ℕ} {S : Garden w} (hS : S.IsPlain)

/-- The nodes of the region of erased attachments: branches of `Tn` and leaves whose leaf pair lies in `Qt`. -/
@[expose] def RegErased (Tn : Finset (GBranch S.tree)) (Qt : Finset (SourcePair S)) (n : GNode S.tree) : Prop :=
  (∃ b ∈ Tn, b.toNode = n) ∨ (∃ ℓ : GLeaf S.tree, ℓ.toNode = n ∧ pairOfLeaf S hS ℓ ∈ Qt)

theorem decoded_completelyPaired {G : Garden w} (D : ReconstructionData S) (hd : D.Decodes hS G)
    (a a' : GNode S.tree) (ha : ∀ b : GBranch S.tree, b.toNode = a → D.tree b = .nil)
    (ha' : ∀ b : GBranch S.tree, b.toNode = a' → D.tree b = .nil)
    (hcp : S.CompletelyPaired (a.leavesBelow ∪ a'.leavesBelow)) :
    G.CompletelyPaired ((D.decodedNode hS hd a).leavesBelow ∪ (D.decodedNode hS hd a').leavesBelow) := by
  intro x hx
  refine ⟨Comb.pair_ne_of_plain hd.1 x, ?_⟩
  rw [Finset.mem_union, leafBelow_iff_below, leafBelow_iff_below] at hx
  rw [Finset.mem_union, leafBelow_iff_below, leafBelow_iff_below]
  rcases hx with hx | hx
  · exact partner_below D hS hd a a' ha hcp x hx
  · rw [Finset.union_comm] at hcp
    exact (partner_below D hS hd a' a ha' hcp x hx).symm

theorem nil_of_regErased {Tn : Finset (GBranch S.tree)} {Qt : Finset (SourcePair S)}
    (E : ReconstructionData S) (hTn : ∀ b ∈ Tn, E.tree b = .nil) {n : GNode S.tree}
    (hn : RegErased hS Tn Qt n) : ∀ b : GBranch S.tree, b.toNode = n → E.tree b = .nil := by
  intro b hb
  rcases hn with ⟨b', hb', hbn⟩ | ⟨ℓ, hℓ, _⟩
  · have : b = b' := by
      have := (nodePieceEquiv S.tree).injective
        (show (nodePieceEquiv S.tree) (.inl b) = (nodePieceEquiv S.tree) (.inl b') from hb.trans hbn.symm)
      exact Sum.inl.inj this
    subst this
    exact hTn b hb'
  · exfalso
    have := (nodePieceEquiv S.tree).injective
      (show (nodePieceEquiv S.tree) (.inl b) = (nodePieceEquiv S.tree) (.inr ℓ) from hb.trans hℓ.symm)
    exact Sum.inl_ne_inr this

theorem layer_decodedNode_le {LH : LayeredGarden w} (E : ReconstructionData S) (he : E.Decodes hS LH.garden)
    {p : ℕ} {kind : Bool} (hc : CanonicalObject p kind LH)
    {Tn : Finset (GBranch S.tree)} {Qt : Finset (SourcePair S)}
    (hTn : ∀ b ∈ Tn, E.tree b = .nil) (hQt : ∀ q ∈ Qt, E.couple q = .triv) {n : GNode S.tree}
    (hn : RegErased hS Tn Qt n) :
    LH.layer (E.decodedNode hS he n) ≤ extendBranchLayers S (inducedPrelayer LH E hS he) p n := by
  rcases hn with ⟨b, hb, rfl⟩ | ⟨ℓ, rfl, hq⟩
  · rw [decodedNode_branch_nil hS E he b (hTn b hb), extendBranchLayers_branch]
    exact le_rfl
  · have hq' := hQt _ hq
    let L := decodedTrivLeaf E hS he ℓ hq'
    have h1 := canonical_leaf_layer LH hc.criterion hc.plain L
    rw [decodedTrivLeaf_pair E hS he ℓ hq'] at h1
    have e1 : L.toNode = E.decodedNode hS he ℓ.toNode := rfl
    have e2 : (decodedTrivLeaf E hS he (S.pair ℓ) (by simpa only [pairOfLeaf_partner] using hq')).toNode =
        E.decodedNode hS he (S.pair ℓ).toNode := rfl
    rw [e2, e1, parentLayer_decodedNode hS LH E he, parentLayer_decodedNode hS LH E he] at h1
    rw [extendBranchLayers_leaf]
    exact h1.le

/-- The canonical pair criterion on the erased region of an object with erased attachments. -/
theorem canonPairs_of_erased {LH : LayeredGarden w} (E : ReconstructionData S) (he : E.Decodes hS LH.garden)
    {p : ℕ} {kind : Bool} (hc : CanonicalObject p kind LH)
    (Tn : Finset (GBranch S.tree)) (Qt : Finset (SourcePair S))
    (hTn : ∀ b ∈ Tn, E.tree b = .nil) (hQt : ∀ q ∈ Qt, E.couple q = .triv) :
    CanonPairs S (inducedPrelayer LH E hS he) p (RegErased hS Tn Qt) := by
  intro a a' ha ha' hinc hcp
  have hI := decodedNode_incomp hS E he a a' hinc
  have hP := decoded_completelyPaired hS E he a a' (nil_of_regErased hS E hTn ha)
    (nil_of_regErased hS E hTn ha') hcp
  have hk := hc.criterion.2 _ _ hI hP
  rw [parentLayer_decodedNode hS LH E he, parentLayer_decodedNode hS LH E he] at hk
  exact hk.trans (max_le_max (layer_decodedNode_le hS E he hc hTn hQt ha)
    (layer_decodedNode_le hS E he hc hTn hQt ha'))

/-- **Region bridge.** For a canonical object `LG` decoding `S` whose regular trees at `T` and couples at `Q` are coherent,
the induced skeleton pre-layering satisfies the canonical pair criterion on the nodes of the region. -/
theorem canonPairs_of_region {LG : LayeredGarden w} (D : ReconstructionData S) (hd : D.Decodes hS LG.garden)
    {p : ℕ} {kind : Bool} (hc : CanonicalObject p kind LG)
    (T : Finset (GBranch S.tree)) (Q : Finset (SourcePair S))
    (hT : ∀ c ∈ T, CohT LG D c) (hQ : ∀ q ∈ Q, CohQ LG D hS q) :
    CanonPairs S (inducedPrelayer LG D hS hd) p (RegErased hS T Q) := by
  obtain ⟨E, LH, he, hc', hnil, htriv, hcore⟩ := erase_region hS T Q LG D hd hc hT hQ
  have := canonPairs_of_erased hS E he hc' T Q hnil htriv
  rw [hcore] at this
  exact this

end WaveTurbulence.LayerCnt
