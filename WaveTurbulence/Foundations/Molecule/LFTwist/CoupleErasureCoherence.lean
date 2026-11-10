/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionIdentityRaw
public import WaveTurbulence.Foundations.Molecule.LFTwist.CanonicalObject

/-! # Coherent couple erasure after the tree attachments have been collapsed -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links

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
