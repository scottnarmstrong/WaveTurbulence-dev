/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftDecorationEquiv
/-! Boundary-labelled top forests and exact restriction of general garden decorations. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

def ForestDecoration {w : ℕ} (top : Fin w → TTree) (d : ℕ) (n : Fin w → (Fin d → ℤ)) : Type :=
  {κ : GNode top → (Fin d → ℤ) // IsBranchConsistent κ ∧ ∀ j, κ (GNode.root top j) = n j}

theorem topNodeEmbedding_root {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (j : Fin w) : topNodeEmbedding top P low (GNode.root top j) =
      GNode.root (graftForest top (blockGraftTrees top P low)) j := rfl

/-- Restrict a general graft decoration to its top forest and each lower garden. Root labels
at the lower gardens are the actual top-leaf labels; flower labels are retained. -/
noncomputable def splitGenDecoration {d w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (κ : GenDecoration (markedGardenGraft sig top P low hsig) d n nfl) :
    Σ κtop : ForestDecoration top d n,
      (B : P.parts) → GenDecoration (low B) d
        (fun k => κtop.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) nfl := by
  have hd := (isDecoration_markedGardenGraft_iff sig top P low hsig κ.1).mp κ.2.1
  let kt : ForestDecoration top d n := ⟨fun a => κ.1 (topNodeEmbedding top P low a),
    hd.1, fun j => κ.2.2.1 j⟩
  refine ⟨kt, fun B => ⟨fun a => κ.1 (lowerNodeEmbedding top P low B a), hd.2 B, ?_, ?_⟩⟩
  · intro k
    exact (congrArg κ.1 (topNodeEmbedding_lower_root top P low B k)).symm
  · intro ℓ hℓ
    have hm := markedGardenGraft_mark_lower sig top P low hsig B ℓ
    have hf : (markedGardenGraft sig top P low hsig).IsFlower (lowerLeafEmbedding top P low B ℓ) :=
      hm.trans hℓ
    have hg := κ.2.2.2 (lowerLeafEmbedding top P low B ℓ) hf
    exact (congrArg κ.1 (gardenLeaf_toNode_lower top P low B ℓ)).symm.trans hg

end WaveTurbulence.Induct
