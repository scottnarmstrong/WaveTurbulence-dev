/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionCoupleUpdate
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionCoupleRootSubtrees
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawPairSite
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedSigns

/-! # The erased couple slot is an actual typed canonical leaf pair of the smaller reconstruction -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseCouple_pairSite {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S) :
    let E := D.eraseCouple p
    (E.raw hS).PairSite (inflatedPosition S E.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S E.tree (p.secondLeaf hS).toNode) := by
  let E := D.eraseCouple p
  let A := inflatedPosition S E.tree (p.firstLeaf hS).toNode
  let B := inflatedPosition S E.tree (p.secondLeaf hS).toNode
  have hfirst : Comb.subtree (E.forest hS A.1) A.2 = some .leaf := by
    have h := E.forest_subtree_pair_first hS p
    rw [D.eraseCouple_at] at h
    exact h
  have hsecond : Comb.subtree (E.forest hS B.1) B.2 = some .leaf := by
    have h := E.forest_subtree_pair_second hS p
    rw [D.eraseCouple_at] at h
    exact h
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h := (Comb.subtree_leaves_iff hfirst []).mp (Finset.mem_singleton_self _)
    simp only [List.append_nil] at h
    exact h
  · have h := (Comb.subtree_leaves_iff hsecond []).mp (Finset.mem_singleton_self _)
    simp only [List.append_nil] at h
    exact h
  · exact (inflatedPosition_sign S E.tree _).trans (sourcePair_first_sign S hS p)
  · exact (inflatedPosition_sign S E.tree _).trans (sourcePair_second_sign S hS p)
  · change (A,B) ∈ E.attachmentPairs hS
    rw [← E.pairList_toFinset hS]
    apply List.mem_toFinset.mpr
    apply E.mem_pairList_couple hS p (A,B)
    rw [D.eraseCouple_at]
    exact List.mem_singleton_self _

end WaveTurbulence.Reg.Skeleton
