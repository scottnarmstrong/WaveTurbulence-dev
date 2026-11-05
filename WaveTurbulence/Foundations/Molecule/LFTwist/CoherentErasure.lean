/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.TreeErasureGarden
public import WaveTurbulence.Foundations.Molecule.LFTwist.TreeCollapseCanonical
public import WaveTurbulence.Foundations.Molecule.LFTwist.CoupleCollapseCanonical
public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructionEmbeddings
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseCoupleCollapseDecodes

/-! # Native coherent attachment erasure in canonical reconstructions

All embedded-object premises are supplied by the actual reconstruction.
The output canonical class is derived from C4, never included as a premise.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links

/-- Erase one coherent native regular tree in a canonical garden. -/
theorem eraseCoherentTree_canonG {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    {p : ℕ} (hc : IsCanonG (p+1) LG) (b : GBranch S.tree)
    (hcoh : CohOn LG ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode))) :
    IsCanonG (p+1) (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b)) := by
  exact collapsePairedTree_isCanonG LG _ hc (D.tree b) (nodeSign S.sig b.1)
    (node3 (fun i => D.inflateNode hS (b.child i))) (D.tree_wf b)
    (reconstruction_chainEmb D hS hd b) hcoh rfl

/-- Erase one coherent native regular couple in a canonical garden. -/
theorem eraseCoherentCouple_canonG {w : ℕ} {S : Garden w} (LG : LayeredGarden w)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    {p : ℕ} (hc : IsCanonG (p+1) LG) (q : SourcePair S)
    (hcoh : CohOn LG ((D.couple q).linksAt (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode))) :
    IsCanonG (p+1) (collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd q) p) := by
  exact collapseCouple_isCanonG LG _ hc (D.couple q) (D.couple_wf q)
    (reconstruction_coupleEmb D hS hd q) hcoh

/-- Source canonical couples satisfy the identical native-tree erasure statement. -/
theorem eraseCoherentTree_canonC {S : Garden 2} (LG : LayeredGarden 2)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    {p : ℕ} (hc : IsCanonC (p+1) LG) (b : GBranch S.tree)
    (hcoh : CohOn LG ((D.tree b).linksAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode))) :
    IsCanonC (p+1) (collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b)) := by
  exact collapsePairedTree_isCanonC _ hc (D.tree b) (nodeSign S.sig b.1)
    (node3 (fun i => D.inflateNode hS (b.child i))) (D.tree_wf b)
    (reconstruction_chainEmb D hS hd b) hcoh rfl

/-- Source canonical couples satisfy native-couple erasure as well. -/
theorem eraseCoherentCouple_canonC {S : Garden 2} (LG : LayeredGarden 2)
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS LG.garden)
    {p : ℕ} (hc : IsCanonC (p+1) LG) (q : SourcePair S)
    (hcoh : CohOn LG ((D.couple q).linksAt (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode))) :
    IsCanonC (p+1) (collapseCoupleLayered LG (D.decoded_couple_isSubCouple hS hd q) p) := by
  exact collapseCouple_isCanonC _ hc (D.couple q) (D.couple_wf q)
    (reconstruction_coupleEmb D hS hd q) hcoh

end WaveTurbulence.LFTwist
