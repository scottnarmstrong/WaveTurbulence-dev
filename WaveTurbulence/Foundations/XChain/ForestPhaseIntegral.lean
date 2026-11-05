/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftDomainIndicator
/-! The phase factor of an arbitrary signed top forest, without any pairing requirement. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

noncomputable def forestPhaseProd {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (k : GNode top → Mom d) (τ : GBranch top → ℝ) : ℂ :=
  ∏ b, Complex.exp ((Real.pi * ((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
    resFactor (k (b.child 0)) (k (b.child 1)) (k (b.child 2)) (k b.toNode) * τ b : ℝ) * Complex.I)

noncomputable def forestPhaseIntegral {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (k : GNode top → Mom d) (p t : ℝ) : ℂ :=
  ∫ τ, (ForestTimeDomain top p t).indicator (forestPhaseProd L γ δ sig top k) τ

theorem markedGardenGraft_phaseProd_eq_forest {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (k : GNode (graftForest top (blockGraftTrees top P low)) → Mom d)
    (τ : GBranch (graftForest top (blockGraftTrees top P low)) → ℝ) :
    phaseProd L γ δ (markedGardenGraft sig top P low hsig) k τ =
      forestPhaseProd L γ δ sig top (fun a => k (topNodeEmbedding top P low a))
        (graftTimeSplit top P low τ).1 *
      ∏ B : P.parts, phaseProd L γ δ (low B) (fun a => k (lowerNodeEmbedding top P low B a))
        (fun b => (graftTimeSplit top P low τ).2 ⟨B, b⟩) :=
  markedGardenGraft_phaseProd L γ δ sig top P low hsig k τ

end WaveTurbulence.Induct
