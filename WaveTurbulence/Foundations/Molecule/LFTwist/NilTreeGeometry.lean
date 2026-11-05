/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.TreeErasureCoherence
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionIdentityRaw

/-! # Once tree attachments are nil, couple roots retain the original source addresses -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links

/-- All regular-tree slots have been erased; regular-couple slots remain arbitrary. -/
@[expose] def TreesNil {w : ℕ} {S : Garden w} (D : ReconstructionData S) : Prop := ∀ b, D.tree b = .nil

theorem nilTrees_position {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hn : TreesNil D)
    (a : GNode S.tree) : inflatedPosition S D.tree a = a.1 := by
  have he : D.tree = (ReconstructionData.identity S).tree := funext hn
  rw [he, inflatedPosition_identity]

theorem nilTrees_corePosition {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hn : TreesNil D)
    (b : GBranch S.tree) : D.corePosition b = b.1 := by
  rw [ReconstructionData.corePosition, hn b, RegChain.lonePath, addrExt_nil, nilTrees_position D hn]
  rfl

/-- Different source pairs have independent endpoints. -/
theorem pairEndpoints_indep {w : ℕ} (S : Garden w) (hS : S.IsPlain) (q r : SourcePair S) (hqr : q ≠ r)
    (l m : GLeaf S.tree) (hl : pairOfLeaf S hS l = q) (hm : pairOfLeaf S hS m = r) : Indep l.1 m.1 := by
  have hne : l ≠ m := fun he => hqr (hl.symm.trans ((congrArg (pairOfLeaf S hS) he).trans hm))
  exact leaves_incomparable hne

/-- Every original branch lies outside every regular-couple attachment. -/
theorem nilTrees_core_outside_couple {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hn : TreesNil D) (q : SourcePair S) (b : GBranch S.tree) :
    ¬ InRegion (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode) (D.corePosition b) := by
  rw [nilTrees_position D hn, nilTrees_position D hn, nilTrees_corePosition D hn]
  rintro (ha | hb)
  · exact leaf_not_above_branch S.tree (q.firstLeaf hS) b ⟨ha.1.symm,ha.2⟩
  · exact leaf_not_above_branch S.tree (q.secondLeaf hS) b ⟨hb.1.symm,hb.2⟩

/-- Every other couple's coherence links lie outside the couple being erased. -/
theorem nilTrees_couple_links_outside {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hn : TreesNil D) (q r : SourcePair S) (hqr : q ≠ r)
    (z : Address w) (hz : z ∈ pairEndpoints ((D.couple q).linksAt
      (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode))) :
    ¬ InRegion (inflatedPosition S D.tree (r.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (r.secondLeaf hS).toNode) z := by
  rw [nilTrees_position D hn, nilTrees_position D hn] at hz ⊢
  have hu := cpl_endpoints_under (D.couple q) (q.firstLeaf hS).1 (q.secondLeaf hS).1 z
    (Finset.mem_union_left _ hz)
  rcases hu with hu | hu
  · rintro (hr | hr)
    · exact (pairEndpoints_indep S hS q r hqr _ _ (pairOfLeaf_firstLeaf S hS q)
        (pairOfLeaf_firstLeaf S hS r)).not_both hu hr
    · exact (pairEndpoints_indep S hS q r hqr _ _ (pairOfLeaf_firstLeaf S hS q)
        (pairOfLeaf_secondLeaf S hS r)).not_both hu hr
  · rintro (hr | hr)
    · exact (pairEndpoints_indep S hS q r hqr _ _ (pairOfLeaf_secondLeaf S hS q)
        (pairOfLeaf_firstLeaf S hS r)).not_both hu hr
    · exact (pairEndpoints_indep S hS q r hqr _ _ (pairOfLeaf_secondLeaf S hS q)
        (pairOfLeaf_secondLeaf S hS r)).not_both hu hr

end WaveTurbulence.LFTwist
