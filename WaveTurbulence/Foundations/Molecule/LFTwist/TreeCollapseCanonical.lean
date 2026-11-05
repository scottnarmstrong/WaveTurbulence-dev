/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.TreeCollapseAgreement

/-! # Coherent paired-tree collapse preserves canonical classes -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links
variable {w : ℕ} (LG : LayeredGarden w) {a b : GNode LG.garden.tree}
    (h : Comb.IsSubPairedTree LG.garden a b)

/-- The retained subtree occurs literally at the old upper address after collapse. -/
theorem collapsePairedTree_subtree :
    Comb.subtree ((collapsePairedTreeGarden h).tree a.1.1) a.1.2 = some (Comb.nodeSubtree b) := by
  change Comb.subtree (Function.update LG.garden.tree a.1.1
    (Comb.replaceAt (LG.garden.tree a.1.1) a.1.2 (Comb.nodeSubtree b)) a.1.1) a.1.2 = _
  rw [Function.update_self]
  exact Comb.subtree_replaceAt (Comb.nodeSubtree_spec a) _

/-- The collapsed attachment is the actual nil regular tree at its retained subtree. -/
theorem collapsePairedTree_embeds_nil (ζ : ℤˣ) :
    ChainEmb (collapsePairedTreeGarden h) .nil ζ a.1 (Comb.nodeSubtree b) where
  node := (Comb.subtree_exists_iff _ _).mp ⟨_,collapsePairedTree_subtree LG h⟩
  tree := subtreeAt_eq_of_subtree _ _ _ (collapsePairedTree_subtree LG h)
  pairs := by
    intro p hp
    simp only [RegChain.pairsAt, List.not_mem_nil] at hp

/-- C4's entire pattern is vacuous for a nil regular tree. -/
theorem nilTreePattern {u : ℕ} (LH : LayeredGarden u) (p : ℕ)
    (ζ : ℤˣ) (a : Address u) : TreePattern LH p .nil ζ a := by
  simp only [TreePattern, CohOn, RegChain.linksAt, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, ChainPairLayers, chainNodesSet,
    RegChain.pairsAt, pairEndpoints_nil, Finset.empty_union,
    Finset.notMem_empty, and_self]

/-- Coherent actual regular-tree collapse preserves canonical gardens. -/
theorem collapsePairedTree_isCanonG {p : ℕ} (hc : IsCanonG (p+1) LG)
    (X : RegChain) (ζ : ℤˣ) (t : TTree) (hwf : X.wf = true)
    (hE : ChainEmb LG.garden X ζ a.1 t) (hcoh : CohOn LG (X.linksAt ζ a.1))
    (hb : b.1 = addrExt a.1 X.lonePath) : IsCanonG (p+1) (collapsePairedTreeLayered LG h) := by
  have hA : OutAgreeT LG (collapsePairedTreeLayered LG h) a.1
      (addrExt a.1 X.lonePath) (addrExt a.1 RegChain.nil.lonePath) := by
    simpa only [← hb, RegChain.lonePath, addrExt_nil] using collapsePairedTree_outAgree LG h
  exact layerreg1_replace_tree_canonG hc hwf hE hcoh hA
    (collapsePairedTree_embeds_nil LG h ζ) (nilTreePattern _ p ζ a.1)

/-- The same coherent actual collapse preserves canonical couples. -/
theorem collapsePairedTree_isCanonC {LG : LayeredGarden 2} {a b : GNode LG.garden.tree}
    (h : Comb.IsSubPairedTree LG.garden a b) {p : ℕ} (hc : IsCanonC (p+1) LG)
    (X : RegChain) (ζ : ℤˣ) (t : TTree) (hwf : X.wf = true)
    (hE : ChainEmb LG.garden X ζ a.1 t) (hcoh : CohOn LG (X.linksAt ζ a.1))
    (hb : b.1 = addrExt a.1 X.lonePath) : IsCanonC (p+1) (collapsePairedTreeLayered LG h) := by
  have hA : OutAgreeT LG (collapsePairedTreeLayered LG h) a.1
      (addrExt a.1 X.lonePath) (addrExt a.1 RegChain.nil.lonePath) := by
    simpa only [← hb, RegChain.lonePath, addrExt_nil] using collapsePairedTree_outAgree LG h
  exact layerreg1_replace_tree_canonC hc hwf hE hcoh hA rfl
    (collapsePairedTree_embeds_nil LG h ζ) (nilTreePattern _ p ζ a.1)

end WaveTurbulence.LFTwist
