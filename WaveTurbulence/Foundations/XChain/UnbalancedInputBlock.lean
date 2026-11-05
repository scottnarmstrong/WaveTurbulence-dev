/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzInputResidual
public import WaveTurbulence.Foundations.XChain.ForestGaugeCharge
public import WaveTurbulence.Foundations.XChain.CumulantOrderedBlock
public import WaveTurbulence.Foundations.XChain.TopPartitionError
/-! The actual input cumulant and lower kernel both vanish on an unbalanced leaf block. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem sum_blockRootEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (B : P.parts)
    {M : Type*} [AddCommMonoid M] (f : GLeaf top → M) :
    (∑ k : Fin B.1.card, f ((blockRootEquiv top P).symm ⟨B, k⟩)) = ∑ a ∈ B.1, f a := by
  have he := Fintype.sum_equiv B.1.equivFin.symm
    (fun k => f (B.1.equivFin.symm k).1) (fun a : ↥B.1 => f a.1) (fun _ => rfl)
  exact he.trans (sum_coe_sort B.1 f)

theorem ansatz_unbalanced_topBlock_zero (Q : WTParams) {Ω : Type*} [MeasurableSpace Ω]
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
    (B : P.parts) (hs : ∑ l ∈ B.1, (nodeSign sig l.1 : ℤ) ≠ 0) (Natt : ℕ) :
    topBlockCumulant (μ.restrict (Fev p)) sig top (fun ω => a ω p) κ B.1 = 0 ∧
      topBlockKernel Q.L Q.γ Q.δ (inputsF Q R) sig top P p Natt κ B = 0 := by
  let ζ : Fin B.1.card → ℤˣ := fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1
  let m : Fin B.1.card → (Fin Q.d → ℤ) := fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode
  have hζ : ∑ k, (ζ k : ℤ) ≠ 0 := by
    have he := sum_blockRootEquiv top P B (fun l => (nodeSign sig l.1 : ℤ))
    exact fun h => hs (he.symm.trans h)
  have he := ansatz_unbalanced_input_residual_zero Q μ g hG hL a Fev R E Et p ha hrapid ζ hζ m
  rw [lowerKernelSum_unbalanced Q.L Q.γ Q.δ (inputsF Q R) ζ p (Q.N p) hζ m, sub_zero] at he
  have hc := cumulant_blockRootEquiv (μ.restrict (Fev p)) top P
    (fun l ω => zpowSign (nodeSign sig l.1) (a ω p (κ.1 l.toNode))) B
  exact ⟨hc.symm.trans he, lowerKernelSum_unbalanced Q.L Q.γ Q.δ (inputsF Q R) ζ p Natt hζ m⟩

end WaveTurbulence.Induct
