/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzBlockOrderBound
public import WaveTurbulence.Foundations.XChain.FiniteProductTailBound
public import WaveTurbulence.Foundations.XChain.PartitionWeightProduct
public import WaveTurbulence.Foundations.XChain.OrderedBlockProducts
public import WaveTurbulence.Foundations.XChain.TopPartitionError
/-! The actual attached-component order tail has geometric decay before decoration summation. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem ansatz_lower_order_product_tail_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : (Fin Q.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom Q.d → ℝ) (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hδ : 0 < Q.δ) (hsmall : Q.δ ^ (Q.ν / 2) ≤ 1 / 2) (hLone : 1 ≤ Q.L)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤
      C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    {n : Fin w → (Fin Q.d → ℤ)} (κ : ForestDecoration top Q.d n)
    (J : ℕ) (hR : ∀ B : P.parts, B.1.card ≤ 2 * Q.R p) :
    ‖∑ orders : P.parts → Fin (Q.N p + 1),
      if J ≤ ∑ B, (orders B).1 then
        ∏ B : P.parts, lowerOrderKernelSum Q.L Q.γ Q.δ (inputsF Q R)
          (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p (Q.N p) (orders B)
          (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)
      else 0‖ ≤
      (C ^ P.parts.card * (∏ l : GLeaf top, jbr (latticePoint Q.L (κ.1 l.toNode))) ^
        (-(Q.Lambda p : ℝ) / 2)) *
        ((Q.δ ^ (Q.ν / 2)) ^ J * 2 ^ P.parts.card) := by
  classical
  have he := norm_sum_pi_product_tail_le (ι := P.parts) (Q.N p + 1) J
    (fun B N => lowerOrderKernelSum Q.L Q.γ Q.δ (inputsF Q R)
      (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p (Q.N p) N
      (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode))
    (fun B => C * (∏ l ∈ B.1, jbr (latticePoint Q.L (κ.1 l.toNode))) ^ (-(Q.Lambda p : ℝ) / 2))
    (fun B => mul_nonneg (by linarith) (Real.rpow_nonneg
      (prod_nonneg (fun l _ => (jbr_pos _).le)) _))
    (Real.rpow_nonneg hδ.le _) hsmall
    (fun B N => ansatz_topBlock_order_kernel_bound Q μ g a Fev R E Et p N ha
      hδ hLone C hC hF sig top P κ B (hR B))
  rw [prod_finpartition_rpow P (fun l => jbr (latticePoint Q.L (κ.1 l.toNode)))
    (fun l _ => (jbr_pos _).le) C (-(Q.Lambda p : ℝ) / 2)] at he
  simpa only [Fintype.card_coe] using he

end WaveTurbulence.Induct
