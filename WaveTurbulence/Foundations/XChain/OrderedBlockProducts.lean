/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantOrderedBlock
/-! Products over the literal ordered enumeration of a partition block. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem prod_ordered_block {α M : Type*} [CommMonoid M] (B : Finset α) (f : α → M) :
    (∏ k : Fin B.card, f (B.equivFin.symm k).1) = ∏ a ∈ B, f a := by
  classical
  exact (Fintype.prod_equiv B.equivFin.symm _ _ (fun _ => rfl)).trans (prod_coe_sort B f)

theorem prod_blockRootEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (B : P.parts)
    {M : Type*} [CommMonoid M] (f : GLeaf top → M) :
    (∏ k : Fin B.1.card, f ((blockRootEquiv top P).symm ⟨B, k⟩)) = ∏ a ∈ B.1, f a := by
  simpa only [blockRootEquiv_symm_eq] using prod_ordered_block B.1 f

end WaveTurbulence.Induct
