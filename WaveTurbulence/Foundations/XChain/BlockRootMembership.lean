/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BlockGraft
/-! The block-root enumeration retains literal membership in its partition block. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem blockRootEquiv_symm_eq {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (B : P.parts) (k : Fin B.1.card) :
    (blockRootEquiv top P).symm ⟨B, k⟩ = (B.1.equivFin.symm k).1 := by
  rfl

theorem blockRootEquiv_symm_mem {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (B : P.parts) (k : Fin B.1.card) :
    (blockRootEquiv top P).symm ⟨B, k⟩ ∈ B.1 := by
  rw [blockRootEquiv_symm_eq]
  exact (B.1.equivFin.symm k).2

theorem blockRootEquiv_block_of_mem {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (B : P.parts)
    (a : GLeaf top) (ha : a ∈ B.1) : (blockRootEquiv top P a).1 = B := by
  apply Subtype.ext
  exact P.part_eq_of_mem B.2 ha

end WaveTurbulence.Induct
