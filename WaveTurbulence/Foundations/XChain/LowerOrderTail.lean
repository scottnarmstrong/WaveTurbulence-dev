/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LowerOrderKernelSum
public import WaveTurbulence.Foundations.XChain.TopCoefficientBounds
/-! The literal attached-order tail series arising from the total-order weighted graft expansion. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def lowerOrderTailIntegrand {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (p Natt J : ℕ) (t : ℝ)
    (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n) : ℂ :=
  (∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j) *
    ∑ orders : P.parts → Fin (Natt + 1),
      if J ≤ ∑ B, (orders B).1 then
        ∏ B : P.parts, lowerOrderKernelSum L γ δ F
          (fun k => nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) p Natt (orders B)
          (fun k => κ.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode)
      else 0

noncomputable def lowerOrderTail {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (p Natt J : ℕ) (t : ℝ)
    (n : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑' κ : ForestDecoration top d n, lowerOrderTailIntegrand L γ δ F sig top P p Natt J t n κ

end WaveTurbulence.Induct
