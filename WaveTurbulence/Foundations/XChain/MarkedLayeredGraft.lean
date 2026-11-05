/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftDecoration
public import WaveTurbulence.Foundations.XChain.LayeredGraft
/-! Layered grafts with arbitrary transported marks. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def markedLayeredGardenGraft {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p) : LayeredGarden w where
  garden := markedGardenGraft sig top P (fun B => (low B).garden) hsig
  layer := graftLayer top P low p
  isLayering := by
    refine ⟨graftLayer_child top P low p hbound, ?_⟩
    intro ℓ
    obtain ⟨⟨B, a⟩, rfl⟩ := (gardenLeafEquiv top P (fun B => (low B).garden)).symm.surjective ℓ
    have hn := gardenLeaf_toNode_lower top P (fun B => (low B).garden) B a
    have hnp := gardenLeaf_toNode_lower top P (fun B => (low B).garden) B ((low B).garden.pair a)
    have hp := markedGardenGraft_pair_lower sig top P (fun B => (low B).garden) hsig B a
    calc
      _ = graftLayer top P low p (gardenNodeEquiv top P (fun B => (low B).garden) (.inr ⟨B, a.toNode⟩)) :=
        congrArg (graftLayer top P low p) hn
      _ = (low B).layer a.toNode := graftLayer_lower top P low p B a.toNode
      _ = (low B).layer ((low B).garden.pair a).toNode := (low B).isLayering.2 a
      _ = graftLayer top P low p (gardenNodeEquiv top P (fun B => (low B).garden)
          (.inr ⟨B, ((low B).garden.pair a).toNode⟩)) :=
        (graftLayer_lower top P low p B ((low B).garden.pair a).toNode).symm
      _ = graftLayer top P low p ((gardenLeafEquiv top P (fun B => (low B).garden)).symm
          ⟨B, (low B).garden.pair a⟩).toNode := congrArg (graftLayer top P low p) hnp.symm
      _ = _ := congrArg (fun ℓ : GLeaf (graftForest top (blockGraftTrees top P (fun B => (low B).garden))) =>
        graftLayer top P low p ℓ.toNode) hp.symm

end WaveTurbulence.Induct
