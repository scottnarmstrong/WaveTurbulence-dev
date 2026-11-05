/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.NilTreeGeometry
public import WaveTurbulence.Foundations.Molecule.LFTwist.CanonicalObject

/-! # Coherent couple erasure after the tree attachments have been collapsed -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links

/-- Erasing a couple changes no tree code. -/
theorem eraseCouple_treesNil {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hn : TreesNil D) (q : SourcePair S) : TreesNil (D.eraseCouple q) := hn

/-- All other couple links keep their layers, because their source leaf pairs are disjoint. -/
theorem eraseCouple_allAttachmentsCoherent {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    {p : ℕ} {kind : Bool} (hc : CanonicalObject p kind LG)
    (hn : TreesNil D) (hall : AllAttachmentsCoherent LG D hS) (r : SourcePair S) :
    AllAttachmentsCoherent (collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd r) p)
      (D.eraseCouple r) hS := by
  let C := collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd r) p
  have hA := collapseCouple_outAgree LG (D.decoded_couple_isSubCouple hS hd r) p hc.criterion hc.plain
  constructor
  · intro b
    change CohOn C ((D.tree b).linksAt _ _)
    rw [hn b]
    simp only [CohOn, RegChain.linksAt, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  · intro q
    by_cases hqr : q = r
    · subst q
      rw [D.eraseCouple_at]
      simp only [CohOn, RegCpl.linksAt, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
    · rw [D.eraseCouple_other r q hqr]
      change CohOn C ((D.couple q).linksAt (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
        (inflatedPosition S D.tree (q.secondLeaf hS).toNode))
      intro l hl
      have ha := nilTrees_couple_links_outside D hS hn q r hqr l.1
        ((mem_pairEndpoints_iff _ _).mpr ⟨l,hl,Or.inl rfl⟩)
      have hb := nilTrees_couple_links_outside D hS hn q r hqr l.2
        ((mem_pairEndpoints_iff _ _).mpr ⟨l,hl,Or.inr rfl⟩)
      exact (hA.layer l.1 ha).symm.trans ((hall.2 q l hl).trans (hA.layer l.2 hb))

/-- Couple erasure keeps every retained original core-branch layer literally unchanged. -/
theorem eraseCouple_inducedPrelayer_eq {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    (q : SourcePair S) (hq : D.couple q ≠ .triv) (p : ℕ) :
    inducedPrelayer (collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd q) p)
      (D.eraseCouple q) hS (D.eraseCouple_collapse_decodes hS hd q hq) = inducedPrelayer LG D hS hd := by
  funext b
  let c := (D.eraseCouple q).decodedCoreBranch hS (D.eraseCouple_collapse_decodes hS hd q hq) b
  change (collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd q) p).layer c.toNode =
    LG.layer (D.decodedCoreBranch hS hd b).toNode
  exact (collapseCoupleLayered_branch LG (D.decoded_couple_isSubCouple hS hd q) p c).trans
    (congrArg LG.layer (congrArg GBranch.toNode (show collapseCoupleBranchEmbedding
      (D.decoded_couple_isSubCouple hS hd q) c = D.decodedCoreBranch hS hd b from Subtype.ext rfl)))

end WaveTurbulence.LFTwist
