/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionRegularTrees
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CoreDeterminesAttachments
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.EmbeddedCarrierRoots

/-! # Replacement data are unique once the actual embedded core is fixed

This conditional helper isolates C1 consumption. Establishing equality of the
embedded cores for arbitrary representations is a separate C3 obligation.
-/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem reconstructionData_eq_of_fixed_core {w : ℕ} {S G : Garden w}
    (D E : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G) (he : E.Decodes hS G)
    (hc : ∀ b, D.corePosition b = E.corePosition b) : D = E := by
  have hupper (a : GNode S.tree) : D.decodedNode hS hd a = E.decodedNode hS he a :=
    Subtype.ext (inflatedPosition_eq_of_corePosition_eq D E hc a)
  have htree : D.tree = E.tree := by
    funext b
    have hcarrier := embeddedPairedTree_eq_of_roots
      (D.decoded_chain_isSubPairedTree hS hd b) (E.decoded_chain_isSubPairedTree hS he b)
      (hupper b.toNode) (Subtype.ext (hc b))
    have hE : (E.tree b).DecodesTree
        (Comb.embeddedPairedTree (D.decoded_chain_isSubPairedTree hS hd b)) :=
      hcarrier.symm ▸ E.decoded_chain_decodes hS he b
    obtain ⟨X,hX,hunique⟩ := existsUnique_regChain_decodesTree _ (D.decoded_chain_regular hS hd b)
    exact (hunique (D.tree b) ⟨D.tree_wf b,D.decoded_chain_decodes hS hd b⟩).trans
      (hunique (E.tree b) ⟨E.tree_wf b,hE⟩).symm
  have hcouple : D.couple = E.couple := by
    funext p
    have hcarrier := subCoupleGarden_eq_of_roots
      (D.decoded_couple_isSubCouple hS hd p) (E.decoded_couple_isSubCouple hS he p)
      (hupper (p.firstLeaf hS).toNode) (hupper (p.secondLeaf hS).toNode)
    have hE : (E.couple p).Decodes
        (Comb.subCoupleGarden (D.decoded_couple_isSubCouple hS hd p)) :=
      hcarrier.symm ▸ E.decoded_couple_decodes hS he p
    obtain ⟨Q,hQ,hunique⟩ := existsUnique_regCpl_decodes _ (D.decoded_couple_regular hS hd p)
    exact (hunique (D.couple p) ⟨D.couple_wf p,D.decoded_couple_decodes hS hd p⟩).trans
      (hunique (E.couple p) ⟨E.couple_wf p,hE⟩).symm
  cases D
  cases E
  cases htree
  cases hcouple
  rfl

end WaveTurbulence.Reg.Skeleton
