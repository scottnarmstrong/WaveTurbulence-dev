/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzInputKernelBound
public import WaveTurbulence.Foundations.XChain.OrderedBlockProducts
public import WaveTurbulence.Foundations.XChain.TopPartitionError
/-! The main lower-kernel bound on each actual graft leaf block. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem ansatz_topBlock_kernel_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : (Fin Q.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom Q.d → ℝ) (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hδ : 0 < Q.δ) (hsmall : Q.δ ^ Q.ν ≤ 1 / 2) (hLone : 1 ≤ Q.L)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF Q R p (latticePoint Q.L n)| ≤
      C * jbr (latticePoint Q.L n) ^ (-(Q.Lambda p : ℝ)))
    {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    {n : Fin w → (Fin Q.d → ℤ)} (κ : ForestDecoration top Q.d n)
    (B : P.parts) (hR : B.1.card ≤ 2 * Q.R p) :
    ‖topBlockKernel Q.L Q.γ Q.δ (inputsF Q R) sig top P p (Q.N p) κ B‖ ≤
      C * (∏ l ∈ B.1, jbr (latticePoint Q.L (κ.1 l.toNode))) ^
        (-(Q.Lambda p : ℝ) / 2) := by
  classical
  have hb : 1 ≤ B.1.card := (P.nonempty_of_mem_parts B.2).card_pos
  have h := ansatz_input_kernel_bound Q μ g a Fev R E Et p ha hLone hδ hsmall C hC hF hb hR
    (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)
  have hp := prod_blockRootEquiv top P B
    (fun l => jbr (latticePoint Q.L (κ.1 l.toNode)))
  rw [hp] at h
  exact h

end WaveTurbulence.Induct
