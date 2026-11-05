/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GardenGraftDescendants
public import WaveTurbulence.Foundations.XChain.PairedEmbedding
/-! Literal lower-garden embeddings and their pairing compatibility. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def lowerLeafEmbedding {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) : GLeaf (low B).tree ↪ GLeaf (graftForest top (blockGraftTrees top P low)) where
  toFun ℓ := (gardenLeafEquiv top P low).symm ⟨B, ℓ⟩
  inj' _ _ h := eq_of_heq (Sigma.mk.inj ((gardenLeafEquiv top P low).symm.injective h)).2

noncomputable def lowerNodeEmbedding {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) : GNode (low B).tree ↪ GNode (graftForest top (blockGraftTrees top P low)) where
  toFun a := gardenNodeEquiv top P low (.inr ⟨B, a⟩)
  inj' _ _ h := eq_of_heq (Sigma.mk.inj (Sum.inr.inj ((gardenNodeEquiv top P low).injective h))).2

theorem lowerLeafEmbedding_pair {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B : P.parts) (ℓ : GLeaf (low B).tree) :
    (gardenGraft sig top P low hplain hsig).pair (lowerLeafEmbedding top P low B ℓ) =
      lowerLeafEmbedding top P low B ((low B).pair ℓ) :=
  gardenGraft_pair_lower sig top P low hplain hsig B ℓ

theorem lowerLeafEmbedding_completelyPaired_iff {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B : P.parts) (S : Finset (GLeaf (low B).tree)) :
    (gardenGraft sig top P low hplain hsig).CompletelyPaired (S.map (lowerLeafEmbedding top P low B)) ↔
      (low B).CompletelyPaired S :=
  completelyPaired_map_iff (low B) (gardenGraft sig top P low hplain hsig)
    (lowerLeafEmbedding top P low B) (lowerLeafEmbedding_pair sig top P low hplain hsig B) S

end WaveTurbulence.Induct
