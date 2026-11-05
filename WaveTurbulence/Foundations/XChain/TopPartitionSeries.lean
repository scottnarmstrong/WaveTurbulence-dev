/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopPartitionError
/-! The two actual partition-series integrands and their explicit local residual. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

noncomputable def topPartitionCumulantIntegrand {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {w d : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (c : Ω → (Fin d → ℤ) → ℂ)
    (p : ℕ) (t : ℝ) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n) : ℂ :=
  (∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j) *
    ∏ B : P.parts, topBlockCumulant μ sig top c κ B.1

noncomputable def topPartitionKernelIntegrand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (p Natt : ℕ) (t : ℝ) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n) : ℂ :=
  (∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j) *
    ∏ B : P.parts, topBlockKernel L γ δ F sig top P p Natt κ B

theorem topPartitionErrorIntegrand_eq_sub {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (c : Ω → (Fin d → ℤ) → ℂ)
    (p Natt : ℕ) (t : ℝ) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n) :
    topPartitionErrorIntegrand μ L γ δ F sig top P c p Natt t n κ =
      topPartitionCumulantIntegrand μ L γ δ sig top P c p t n κ -
      topPartitionKernelIntegrand L γ δ F sig top P p Natt t n κ := by
  exact mul_sub _ _ _

end WaveTurbulence.Induct
