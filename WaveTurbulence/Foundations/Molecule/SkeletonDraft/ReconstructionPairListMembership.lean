/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairList

/-! # Literal component membership in the full reconstruction pair list -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.mem_pairList_couple {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (p : SourcePair S) (q : Pair w)
    (hq : q ∈ (D.couple p).pairsAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode)) : q ∈ D.pairList hS := by
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨p,Finset.mem_toList.mpr (Finset.mem_univ _),hq⟩

theorem ReconstructionData.mem_pairList_chain {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) (q : Pair w)
    (hq : q ∈ (D.tree b).pairsAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)) :
    q ∈ D.pairList hS := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨b,Finset.mem_toList.mpr (Finset.mem_univ _),hq⟩

theorem ReconstructionData.pairList_mem_cases {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (q : Pair w) (hq : q ∈ D.pairList hS) :
    (∃ p : SourcePair S, q ∈ (D.couple p).pairsAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode)) ∨
    (∃ b : GBranch S.tree, q ∈ (D.tree b).pairsAt (nodeSign S.sig b.1)
      (inflatedPosition S D.tree b.toNode)) := by
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp h
    exact Or.inl ⟨p,hp⟩
  · obtain ⟨b,_,hb⟩ := List.mem_flatMap.mp h
    exact Or.inr ⟨b,hb⟩

end WaveTurbulence.Reg.Skeleton
