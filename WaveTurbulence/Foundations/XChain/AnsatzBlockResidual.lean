/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzInputResidual
public import WaveTurbulence.Foundations.XChain.OrderedBlockProducts
public import WaveTurbulence.Foundations.XChain.TopPartitionError
/-! Actual induction-hypothesis residual on each ordered leaf block of the graft expansion. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem ansatz_topBlock_residual_bound (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : (Fin Q.d → ℤ) → Ω → ℂ)
    (hG : IsGaussianData μ g) (hL : 0 < Q.L)
    (a : Ω → ℝ → (Fin Q.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom Q.d → ℝ) (E : ℕ → (Fin Q.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin Q.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt Q μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff Q.L Q.φin g ω))
    {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top)))
    {n : Fin w → (Fin Q.d → ℤ)} (κ : ForestDecoration top Q.d n)
    (B : P.parts) (hR : B.1.card ≤ 2 * Q.R p) :
    ‖topBlockCumulant (μ.restrict (Fev p)) sig top (fun ω => a ω p) κ B.1 -
      topBlockKernel Q.L Q.γ Q.δ (inputsF Q R) sig top P p (Q.N p) κ B‖ ≤
      (∏ l ∈ B.1, jbr (latticePoint Q.L (κ.1 l.toNode))) ^
        (-(Q.Lambda p : ℝ) / 2) * Real.exp (-(Q.N p : ℝ)) := by
  classical
  have hb : 1 ≤ B.1.card := (P.nonempty_of_mem_parts B.2).card_pos
  have h := ansatz_input_residual_bound Q μ g hG hL a Fev R E Et p ha hrapid hb hR
    (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)
  have hc := cumulant_blockRootEquiv (μ.restrict (Fev p)) top P
    (fun l ω => zpowSign (nodeSign sig l.1) (a ω p (κ.1 l.toNode))) B
  have hp := prod_blockRootEquiv top P B
    (fun l => jbr (latticePoint Q.L (κ.1 l.toNode)))
  rw [hc, hp] at h
  exact h

end WaveTurbulence.Induct
