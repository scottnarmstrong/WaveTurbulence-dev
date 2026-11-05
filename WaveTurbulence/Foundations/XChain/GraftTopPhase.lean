/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftFlowerFreeTimes
public import WaveTurbulence.Foundations.XChain.ForestPhaseIntegral
/-! The phase function of an arbitrary top forest with retained prescribed flower times. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open scoped Classical

noncomputable def graftTopPhaseFn {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (k : GNode top → Mom d) (p t s : ℝ) (τ : GraftTopFreeBranch sig top P low hsig → ℝ) : ℂ :=
  (ForestTimeDomain top p t).indicator (forestPhaseProd L γ δ sig top k)
    (graftTopExtendTime sig top P low hsig s τ)

noncomputable def graftTopPhaseIntegral {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (k : GNode top → Mom d) (p t s : ℝ) : ℂ :=
  ∫ τ, graftTopPhaseFn L γ δ sig top P low hsig k p t s τ

noncomputable def lowerPhaseIndicatorProduct {d : ℕ} {β : Type*} [Fintype β]
    {v : β → ℕ} (L γ δ : ℝ) (low : (B : β) → LayeredGarden (v B)) (p s : ℝ)
    (k : (B : β) → GNode (low B).garden.tree → Mom d)
    (τ : (Σ B : β, GBranch (low B).garden.tree) → ℝ) : ℂ :=
  ∏ B, (kDomain (low B) (fun _ => p) s).indicator (phaseProd L γ δ (low B).garden (k B))
    (fun b => τ ⟨B, b⟩)

end WaveTurbulence.Induct
