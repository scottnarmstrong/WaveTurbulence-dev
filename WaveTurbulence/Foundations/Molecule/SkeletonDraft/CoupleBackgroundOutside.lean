/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionCoupleBackground
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseCouplePairSite
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.CoupleRootPairTriviality
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawPairEndpointExclusion

/-! # Unchanged matching blocks lie outside both inserted couple roots -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.coupleBackground_not_below {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S) (hQ : D.couple p ≠ .triv)
    (q : Pair w) (hq : q ∈ D.coupleBackground hS p) :
    let A := inflatedPosition S D.tree (p.firstLeaf hS).toNode
    let B := inflatedPosition S D.tree (p.secondLeaf hS).toNode
    ¬ Below A q.1 ∧ ¬ Below B q.1 := by
  let E := D.eraseCouple p
  let A := inflatedPosition S D.tree (p.firstLeaf hS).toNode
  let B := inflatedPosition S D.tree (p.secondLeaf hS).toNode
  have he : q ∈ (E.raw hS).pairs := by
    change q ∈ E.attachmentPairs hS
    rw [E.attachmentPairs_eq_background_union hS p,D.eraseCouple_background hS p]
    exact Finset.mem_union_left _ hq
  have hn : q ≠ (A,B) := by
    intro hh
    apply hQ
    apply D.couple_eq_triv_of_root_pair_mem hS p
    change (A,B) ∈ D.attachmentPairs hS
    rw [D.attachmentPairs_eq_background_union hS p]
    exact Finset.mem_union_left _ (hh ▸ hq)
  have hv := (E.raw_valid hS).1 q he
  have hs := D.eraseCouple_pairSite hS p
  have hne := (E.raw_valid hS).pair_ne_endpoints hs q he hn
  have ha (x : Address w) (hx : x.2 ∈ ((E.raw hS).tree x.1).leaves) (hne : x ≠ q.1) : ¬ Below x q.1 := by
    intro hh
    have hleaf : q.1.2 ∈ ((E.raw hS).tree x.1).leaves := hh.1 ▸ hv.1
    have hp := leaf_prefix_node_eq hx (TTree.leaves_subset_nodes _ hleaf) hh.2
    exact hne (Prod.ext hh.1.symm hp)
  exact ⟨ha A hs.leftLeaf (Ne.symm hne.1),ha B hs.rightLeaf (Ne.symm hne.2.1)⟩

end WaveTurbulence.Reg.Skeleton
