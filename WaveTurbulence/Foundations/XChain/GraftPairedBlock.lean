/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerPairedSubtrees
public import WaveTurbulence.Foundations.Canon.Basic
/-! A completely paired union of two lower subtrees must lie in a single lower block. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem lower_block_eq_of_paired_subtrees {w : ℕ} (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card) (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B C : P.parts) (a : GNode (low B).tree) (b : GNode (low C).tree)
    (hcp : (gardenGraft sig top P low hplain hsig).CompletelyPaired
      ((lowerNodeEmbedding top P low B a).leavesBelow ∪
       (lowerNodeEmbedding top P low C b).leavesBelow)) : B = C := by
  classical
  by_contra hBC
  have hsingle : (low B).CompletelyPaired a.leavesBelow := by
    intro ℓ hℓ
    have hm := (mem_lower_leavesBelow_iff top P low B a ℓ).mpr hℓ
    obtain ⟨hne, hp⟩ := hcp (lowerLeafEmbedding top P low B ℓ) (mem_union_left _ hm)
    have he := lowerLeafEmbedding_pair sig top P low hplain hsig B ℓ
    have hp' : lowerLeafEmbedding top P low B ((low B).pair ℓ) ∈
        (lowerNodeEmbedding top P low B a).leavesBelow ∪
        (lowerNodeEmbedding top P low C b).leavesBelow := he ▸ hp
    refine ⟨fun hz => hne (he.trans (congrArg (lowerLeafEmbedding top P low B) hz)), ?_⟩
    rcases mem_union.mp hp' with hl | hr
    · exact (mem_lower_leavesBelow_iff top P low B a _).mp hl
    · exact False.elim (not_mem_lower_leavesBelow_of_blocks_ne top P low C B
        (Ne.symm hBC) b _ hr)
  exact (Nat.not_even_iff_odd.mpr (Canon.odd_card_leavesBelow a))
    (Canon.even_card_of_completelyPaired (low B) _ _ rfl hsingle)

end WaveTurbulence.Induct
