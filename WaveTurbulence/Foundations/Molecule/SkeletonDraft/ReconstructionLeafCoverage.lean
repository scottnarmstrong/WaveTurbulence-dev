/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionLeafPairCoverage
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.LeafAddressesNode3
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedCoreBranches

/-! # Every leaf of the literal reconstructed forest is covered by a listed code pair -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.inflateNode_pairList_cover {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (a : GNode S.tree) (z : Address w)
    (hz : z ∈ leafAddresses (D.inflateNode hS a) (inflatedPosition S D.tree a)) :
    z ∈ pairEndpoints (D.pairList hS) := by
  cases hs : Comb.nodeSubtree a with
  | leaf =>
    let ℓ := leafOfSubtree a hs
    have ha : ℓ.toNode = a := Subtype.ext rfl
    apply D.leafTree_pairList_cover hS ℓ z
    have he : D.inflateNode hS a = D.leafTree hS ℓ :=
      (congrArg (D.inflateNode hS) ha.symm).trans (D.inflateNode_leaf hS ℓ)
    exact (congrArg₂ leafAddresses he (congrArg (inflatedPosition S D.tree) ha.symm)) ▸ hz
  | node l m r =>
    let b := branchOfSubtree a l m r hs
    have hb : b.toNode = a := Subtype.ext rfl
    have hsub : z ∈ leafAddresses (D.inflateNode hS b.toNode) (inflatedPosition S D.tree b.toNode) :=
      (congrArg (fun a => z ∈ leafAddresses (D.inflateNode hS a) (inflatedPosition S D.tree a)) hb.symm) ▸ hz
    rw [D.inflateNode_branch,chain_leafAddresses] at hsub
    rcases Finset.mem_union.mp hsub with hp | hc
    · obtain ⟨q,hq,he⟩ := (mem_pairEndpoints_iff _ _).mp hp
      exact (mem_pairEndpoints_iff _ _).mpr ⟨q,D.mem_pairList_chain hS b q hq,he⟩
    · obtain ⟨i,hi⟩ := (mem_leafAddresses_node3 _ _ z).mp hc
      have hpos : addrExt (addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath) [i] =
          inflatedPosition S D.tree (b.child i) := (D.core_child_position b i).symm
      have hleaf : z ∈ leafAddresses (D.inflateNode hS (b.child i)) (inflatedPosition S D.tree (b.child i)) :=
        (congrArg (fun a => z ∈ leafAddresses (D.inflateNode hS (b.child i)) a) hpos) ▸ hi
      exact D.inflateNode_pairList_cover hS (b.child i) z hleaf
termination_by (Comb.nodeSubtree a).order
decreasing_by exact nodeSubtree_child_order_lt S.tree _ _

theorem ReconstructionData.forest_pairList_cover {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (ℓ : GLeaf (D.forest hS)) :
    ℓ.1 ∈ pairEndpoints (D.pairList hS) := by
  apply D.inflateNode_pairList_cover hS (GNode.root S.tree ℓ.1.1) ℓ.1
  rw [inflatedPosition_root]
  exact Finset.mem_image.mpr ⟨ℓ.1.2,ℓ.2,by simp [addrExt]⟩

end WaveTurbulence.Reg.Skeleton
