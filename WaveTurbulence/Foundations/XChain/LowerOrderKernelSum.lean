/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FiniteOrderGrouping
/-! Exact order grouping of the actual attached-garden kernels, including cutoff weights. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def lowerOrderKernelSum {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (p Natt : ℕ) (N : Fin (Natt + 1))
    (n : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑ D : LowerGraftData sig p Natt,
    if D.low.garden.order = N.1 then KG L γ δ F D.low p n else 0

theorem sum_lowerFamily_by_orders {w d p Natt : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    {n : Fin w → (Fin d → ℤ)} (κ : ForestDecoration top d n)
    (W : (P.parts → Fin (Natt + 1)) → ℂ) :
    (∑ low : LowerFamily sig top P p Natt,
      W (fun B => ⟨(low B).low.garden.order, Nat.lt_succ_of_le (low B).order_le⟩) *
        ∏ B : P.parts, KG L γ δ F (low B).low p
          (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)) =
      ∑ orders : P.parts → Fin (Natt + 1), W orders *
        ∏ B : P.parts, lowerOrderKernelSum L γ δ F
          (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt (orders B)
          (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) := by
  classical
  have he := sum_pi_by_orders
    (fun (B : P.parts) (D : LowerGraftData
      (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt) =>
        (⟨D.low.garden.order, Nat.lt_succ_of_le D.order_le⟩ : Fin (Natt + 1)))
    (fun (B : P.parts) (D : LowerGraftData
      (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt) =>
        KG L γ δ F D.low p (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)) W
  simpa only [Fin.ext_iff, lowerOrderKernelSum] using he

end WaveTurbulence.Induct
