/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BlockGraftPairing
/-! Exact order bookkeeping for the canonical garden grafting, including all lower blocks. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem sum_forest_leaves {w : ℕ} (top : Fin w → TTree) (f : Fin w → TTree.Path → ℕ) :
    (∑ a : GLeaf top, f a.1.1 a.1.2) = ∑ j, ∑ a ∈ (top j).leaves, f j a := by
  have h := Fintype.sum_equiv (forestLeafSigmaEquiv top)
    (fun a : GLeaf top => f a.1.1 a.1.2)
    (fun a : Σ j : Fin w, ↥(top j).leaves => f a.1 a.2.1) (fun _ => rfl)
  simpa only [Fintype.sum_sigma, Finset.sum_coe_sort] using h

theorem sum_lower_root_orders {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    (∑ a : GLeaf top, ((low (blockRootEquiv top P a).1).tree (blockRootEquiv top P a).2).order) =
      ∑ B : P.parts, (low B).order := by
  have h := Fintype.sum_equiv (blockRootEquiv top P)
    (fun a : GLeaf top => ((low (blockRootEquiv top P a).1).tree (blockRootEquiv top P a).2).order)
    (fun a : Σ B : P.parts, Fin B.1.card => ((low a.1).tree a.2).order) (fun _ => rfl)
  simpa only [Fintype.sum_sigma, Garden.order] using h

/-- The order is exactly the sum of top-tree orders and lower-garden orders. -/
theorem gardenGraft_order {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) :
    (gardenGraft sig top P low hplain hsig).order =
      (∑ j, (top j).order) + ∑ B : P.parts, (low B).order := by
  change (∑ j, (graftTree (top j) (blockGraftTrees top P low j)).order) = _
  simp_rw [graftTree_order]
  rw [Finset.sum_add_distrib, ← sum_forest_leaves]
  have he (a : GLeaf top) : (blockGraftTrees top P low a.1.1 a.1.2).order =
      ((low (blockRootEquiv top P a).1).tree (blockRootEquiv top P a).2).order :=
    congrArg TTree.order (blockGraftTrees_at_leaf top P low a)
  simp_rw [he]
  rw [sum_lower_root_orders]

end WaveTurbulence.Induct
