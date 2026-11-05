/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftLowerCriterion
/-! Canonicality of the concrete top-layer graft, including the zero-order pair components. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem layeredGardenGraft_criterion {w : ℕ} (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hplain : ∀ B, (low B).garden.IsPlain)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hcomponent : ∀ B, IsCanonG p (low B) ∨ ∀ a, (low B).layer a = p) :
    (layeredGardenGraft sig top P low p hplain hsig hbound).CanonCriterion p := by
  let big := layeredGardenGraft sig top P low p hplain hsig hbound
  have hl : ∀ a : GNode big.garden.tree, big.layer a ≤ p :=
    graftLayer_le top P low p hbound
  refine ⟨hl, ?_⟩
  intro a b hinc hcp
  obtain ⟨za, rfl⟩ := (gardenNodeEquiv top P (fun B => (low B).garden)).surjective a
  obtain ⟨zb, rfl⟩ := (gardenNodeEquiv top P (fun B => (low B).garden)).surjective b
  rcases za with a | ⟨B, a⟩
  · have ha := graftLayer_top top P low p a
    exact (min_le_left _ _).trans ((parentLayer_le_of_layer_le big p hl _).trans
      (ha.symm.le.trans (le_max_left _ _)))
  · rcases zb with b | ⟨C, b⟩
    · have hb := graftLayer_top top P low p b
      exact (min_le_right _ _).trans ((parentLayer_le_of_layer_le big p hl _).trans
        (hb.symm.le.trans (le_max_right _ _)))
    · have hBC := lower_block_eq_of_paired_subtrees sig top P
        (fun B => (low B).garden) hplain hsig B C a b hcp
      subst C
      have ham := graftLayer_lower top P low p B a
      have hbm := graftLayer_lower top P low p B b
      have hm := congrArg₂ max ham hbm
      have hh : min (big.parentLayer p
          (lowerNodeEmbedding top P (fun B => (low B).garden) B a))
          (big.parentLayer p (lowerNodeEmbedding top P (fun B => (low B).garden) B b)) ≤
          max ((low B).layer a) ((low B).layer b) := by
        rcases hcomponent B with hc | hp
        · exact graft_lower_criterion sig top P low p hplain hsig hbound B hc a b hinc hcp
        · exact (min_le_left _ _).trans ((parentLayer_le_of_layer_le big p hl _).trans
            ((hp a).symm.le.trans (le_max_left _ _)))
      exact hh.trans hm.symm.le

end WaveTurbulence.Induct
