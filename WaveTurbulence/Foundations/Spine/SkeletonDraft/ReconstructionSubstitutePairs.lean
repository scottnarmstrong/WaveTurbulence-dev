/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionSubstitutePair
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionPairBlocks
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.FiniteBlockSplice

/-! # Exact complete pair-set substitution under a global regular-couple replacement -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.substitutePair_block_mem {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (x y : Address w) (Q : RegCpl)
    (i : ReplacementSlot S) (q : Pair w) :
    q ∈ (D.substitutePair hS x y Q).pairBlock hS i ↔
      (q ∈ D.pairBlock hS i ∧ q ≠ (x,y)) ∨
      ((x,y) ∈ D.pairBlock hS i ∧ q ∈ (Q.pairsAt x y).toFinset) := by
  cases i with
  | inl p =>
    change q ∈ (((D.substitutePair hS x y Q).couple p).pairsAt _ _).toFinset ↔ _
    rw [D.substitutePair_position,D.substitutePair_position]
    change q ∈ ((normalizeCouple (substituteCouplePair (D.couple p) _ _ x y Q)).pairsAt _ _).toFinset ↔ _
    simp only [List.mem_toFinset,mem_normalizeCouple_pairsAt,mem_substituteCouplePair]
    simp only [ReconstructionData.pairBlock,List.mem_toFinset]
  | inr b =>
    change q ∈ (((D.substitutePair hS x y Q).tree b).pairsAt _ _).toFinset ↔ _
    rw [D.substitutePair_position]
    change q ∈ ((normalizeChain (substituteChainPair (D.tree b) _ _ x y Q)).pairsAt _ _).toFinset ↔ _
    simp only [List.mem_toFinset,mem_normalizeChain_pairsAt,mem_substituteChainPair]
    simp only [ReconstructionData.pairBlock,List.mem_toFinset]

theorem ReconstructionData.substitutePair_pairs {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (x y : Address w) (Q : RegCpl)
    (hp : (x,y) ∈ D.attachmentPairs hS) :
    (D.substitutePair hS x y Q).attachmentPairs hS =
      (D.attachmentPairs hS).erase (x,y) ∪ (Q.pairsAt x y).toFinset := by
  rw [(D.substitutePair hS x y Q).attachmentPairs_eq_blocks]
  have he := biUnion_pair_substitution (D.pairBlock hS) ((D.substitutePair hS x y Q).pairBlock hS)
    (x,y) (Q.pairsAt x y).toFinset (D.substitutePair_block_mem hS x y Q)
  rw [← D.attachmentPairs_eq_blocks hS,ite_eq_left hp] at he
  exact he

end WaveTurbulence.Reg.Skeleton
