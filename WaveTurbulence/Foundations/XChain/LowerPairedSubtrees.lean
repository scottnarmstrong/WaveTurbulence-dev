/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerLeavesBelow
/-! Pairing closure of lower subtree unions is preserved by garden grafting. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem lower_subtrees_completelyPaired_iff {w : ℕ} (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card) (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B : P.parts) (a b : GNode (low B).tree) :
    (gardenGraft sig top P low hplain hsig).CompletelyPaired
      ((lowerNodeEmbedding top P low B a).leavesBelow ∪
       (lowerNodeEmbedding top P low B b).leavesBelow) ↔
    (low B).CompletelyPaired (a.leavesBelow ∪ b.leavesBelow) := by
  have he : (lowerNodeEmbedding top P low B a).leavesBelow ∪
      (lowerNodeEmbedding top P low B b).leavesBelow =
      (a.leavesBelow ∪ b.leavesBelow).map (lowerLeafEmbedding top P low B) := by
    rw [lower_leavesBelow_eq_map, lower_leavesBelow_eq_map, Finset.map_union]
  exact (congrArg (gardenGraft sig top P low hplain hsig).CompletelyPaired he).to_iff.trans
    (lowerLeafEmbedding_completelyPaired_iff sig top P low hplain hsig B _)

end WaveTurbulence.Induct
