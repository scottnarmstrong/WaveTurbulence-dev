/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairListMembership
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairLeafRecovery

/-! # Every replacement leaf below a source leaf belongs to its shared couple pair block -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.leafTree_pairList_cover {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (ℓ : GLeaf S.tree) (z : Address w)
    (hz : z ∈ leafAddresses (D.leafTree hS ℓ) (inflatedPosition S D.tree ℓ.toNode)) :
    z ∈ pairEndpoints (D.pairList hS) := by
  let p := pairOfLeaf S hS ℓ
  have hblock : z ∈ pairEndpoints ((D.couple p).pairsAt
      (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode)) := by
    rw [← couple_leafAddresses]
    by_cases hℓ : nodeSign S.sig ℓ.1 = 1
    · have he : p.firstLeaf hS = ℓ := pairOfLeaf_first_of_positive S hS ℓ hℓ
      rw [he]
      apply Finset.mem_union_left
      simpa only [ReconstructionData.leafTree,treeOfSign,ite_eq_left hℓ] using hz
    · have he : p.secondLeaf hS = ℓ := pairOfLeaf_second_of_negative S hS ℓ hℓ
      rw [he]
      apply Finset.mem_union_right
      simpa only [ReconstructionData.leafTree,treeOfSign,ite_eq_right hℓ] using hz
  obtain ⟨q,hq,he⟩ := (mem_pairEndpoints_iff _ _).mp hblock
  exact (mem_pairEndpoints_iff _ _).mpr ⟨q,D.mem_pairList_couple hS p q hq,he⟩

end WaveTurbulence.Reg.Skeleton
