/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftInputEquiv
public import WaveTurbulence.Foundations.XChain.GardenGraftOrder
/-! Input factors and coupling powers of the generic marked-garden graft. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem markedGardenGraft_order {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) :
    (markedGardenGraft sig top P low hsig).order =
      (∑ j, (top j).order) + ∑ B : P.parts, (low B).order := by
  change (∑ j, (graftTree (top j) (blockGraftTrees top P low j)).order) = _
  simp_rw [graftTree_order]
  rw [Finset.sum_add_distrib, ← sum_forest_leaves]
  have he (a : GLeaf top) : (blockGraftTrees top P low a.1.1 a.1.2).order =
      ((low (blockRootEquiv top P a).1).tree (blockRootEquiv top P a).2).order :=
    congrArg TTree.order (blockGraftTrees_at_leaf top P low a)
  simp_rw [he]
  rw [sum_lower_root_orders]

theorem markedLayeredGardenGraft_inputs {d w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p) (F : ℕ → Mom d → ℝ)
    (k : GNode (graftForest top (blockGraftTrees top P (fun B => (low B).garden))) → Mom d) :
    (∏ ℓ ∈ inputLeaves (markedLayeredGardenGraft sig top P low p hsig hbound).garden,
      (F ((markedLayeredGardenGraft sig top P low p hsig hbound).layer ℓ.toNode) (k ℓ.toNode) : ℂ)) =
    ∏ B : P.parts, ∏ ℓ ∈ inputLeaves (low B).garden,
      (F ((low B).layer ℓ.toNode)
        (k (lowerNodeEmbedding top P (fun B => (low B).garden) B ℓ.toNode)) : ℂ) := by
  have he := prod_graft_inputLeaves sig top P (fun B => (low B).garden) hsig
    (fun ℓ => (F ((markedLayeredGardenGraft sig top P low p hsig hbound).layer ℓ.toNode)
      (k ℓ.toNode) : ℂ))
  apply he.trans
  apply Finset.prod_congr rfl
  intro B _
  apply Finset.prod_congr rfl
  intro ℓ _
  have hl := markedLayeredGardenGraft_leaf_layer sig top P low p hsig hbound B ℓ
  have hk := congrArg k (gardenLeaf_toNode_lower top P (fun B => (low B).garden) B ℓ)
  exact congrArg (fun r : ℝ => (r : ℂ)) (congrArg₂ F hl hk)

end WaveTurbulence.Induct
