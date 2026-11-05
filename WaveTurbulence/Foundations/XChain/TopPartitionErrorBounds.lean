/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopPartitionErrorConvergence
/-! Quantitative input-error factor retained by every actual cmattr partition integrand. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem norm_topPartitionErrorIntegrand_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (c : Ω → (Fin d → ℤ) → ℂ)
    (p Natt : ℕ) (t : ℝ) (n : Fin w → (Fin d → ℤ)) (κ : ForestDecoration top d n)
    (M : P.parts → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hM : ∀ B, 0 ≤ M B)
    (hmain : ∀ B, ‖topBlockKernel L γ δ F sig top P p Natt κ B‖ ≤ M B)
    (herr : ∀ B, ‖topBlockCumulant μ sig top c κ B.1 - topBlockKernel L γ δ F sig top P p Natt κ B‖ ≤ ε * M B) :
    ‖topPartitionErrorIntegrand μ L γ δ F sig top P c p Natt t n κ‖ ≤
      (∏ j, SysAPI.boxVol (top j) p t) * (2 ^ P.parts.card * ε * ∏ B : P.parts, M B) := by
  have hp := norm_prod_difference_le (univ : Finset P.parts)
    (fun B : P.parts => topBlockCumulant μ sig top c κ B.1)
    (fun B : P.parts => topBlockKernel L γ δ F sig top P p Natt κ B) M hε hε1
    (fun B _ => hM B) (fun B _ => hmain B) (fun B _ => herr B)
  simp only [card_univ, Fintype.card_coe] at hp
  unfold topPartitionErrorIntegrand
  rw [norm_mul]
  exact mul_le_mul (norm_prod_topTreeCoefficient_le L γ δ p top sig n κ (fun _ => t)) hp
    (norm_nonneg _) (prod_nonneg (fun j _ => SysAPI.boxVol_nonneg (top j) p t))

end WaveTurbulence.Induct
