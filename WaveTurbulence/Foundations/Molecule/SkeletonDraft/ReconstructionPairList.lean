/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionDataCount
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.FiniteBlockLists

/-! # Exact pair-list enumeration and endpoint count of a literal reconstruction -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Enumerate every complete internal code pair block, once at its original source slot. -/
noncomputable def ReconstructionData.pairList {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : List (Pair w) :=
  Finset.univ.toList.flatMap (fun p : SourcePair S =>
    (D.couple p).pairsAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode)) ++
  Finset.univ.toList.flatMap (fun b : GBranch S.tree =>
    (D.tree b).pairsAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode))

theorem ReconstructionData.pairList_toFinset {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) : (D.pairList hS).toFinset = D.attachmentPairs hS := by
  rw [ReconstructionData.pairList,List.toFinset_append,toFinset_univ_flatMap,toFinset_univ_flatMap]
  rfl

theorem ReconstructionData.pairList_length {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) :
    (D.pairList hS).length = D.size + Fintype.card (SourcePair S) := by
  rw [ReconstructionData.pairList,List.length_append,length_univ_flatMap,length_univ_flatMap]
  simp only [couple_pairsAt_length,chain_pairsAt_length,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one]
  unfold ReconstructionData.size
  omega

end WaveTurbulence.Reg.Skeleton
