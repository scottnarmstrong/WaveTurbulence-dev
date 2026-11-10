/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerFamilySeriesConvergence
public import WaveTurbulence.Foundations.XChain.ForestPartitionConvergence
public import WaveTurbulence.Foundations.XChain.BlockProductError
/-! The concrete T.cmattr error on a leaf partition: at least one input-cumulant residual. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

noncomputable def topBlockCumulant {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {w d : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree) (c : Ω → (Fin d → ℤ) → ℂ)
    {n : Fin w → (Fin d → ℤ)} (κ : ForestDecoration top d n) (B : Finset (GLeaf top)) : ℂ :=
  cumulant μ (fun l ω => zpowSign (nodeSign sig l.1) (c ω (κ.1 l.toNode))) B

noncomputable def topBlockKernel {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (p Natt : ℕ) {n : Fin w → (Fin d → ℤ)} (κ : ForestDecoration top d n) (B : P.parts) : ℂ :=
  lowerKernelSum L γ δ F (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt
    (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)

noncomputable def topPartitionErrorIntegrand {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (c : Ω → (Fin d → ℤ) → ℂ)
    (p Natt : ℕ) (t : ℝ) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n) : ℂ :=
  (∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j) *
    ((∏ B : P.parts, topBlockCumulant μ sig top c κ B.1) -
      ∏ B : P.parts, topBlockKernel L γ δ F sig top P p Natt κ B)

noncomputable def topPartitionError {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (c : Ω → (Fin d → ℤ) → ℂ)
    (p Natt : ℕ) (t : ℝ) (n : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑' κ : ForestDecoration top d n, topPartitionErrorIntegrand μ L γ δ F sig top P c p Natt t n κ

end WaveTurbulence.Induct
