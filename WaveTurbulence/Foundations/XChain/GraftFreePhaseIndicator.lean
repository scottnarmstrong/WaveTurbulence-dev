/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftTopPhase
public import WaveTurbulence.Foundations.XChain.GraftPhaseIndicator
/-! The pointwise phase-domain identity on the actual free branching coordinates. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem phaseIndicator_freeGraft {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (hf : ∀ B b, ¬ (low B).garden.IsFlowerParent b)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (k : GNode (graftForest top (blockGraftTrees top P (fun B => (low B).garden))) → Mom d)
    (τ : (markedGardenGraft sig top P (fun B => (low B).garden) hsig).FreeBranch → ℝ) :
    (kDomain (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) s).indicator
      (phaseProd L γ δ (markedGardenGraft sig top P (fun B => (low B).garden) hsig) k)
      ((markedGardenGraft sig top P (fun B => (low B).garden) hsig).extendTime s τ) =
    graftTopPhaseFn L γ δ sig top P (fun B => (low B).garden) hsig
      (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a)) p t s
      (graftFlowerFreeTimeSplit sig top P (fun B => (low B).garden) hsig hf τ).1 *
    lowerPhaseIndicatorProduct L γ δ low p s
      (fun B a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a))
      (graftFlowerFreeTimeSplit sig top P (fun B => (low B).garden) hsig hf τ).2 := by
  have hi := phaseIndicator_markedGraft L γ δ sig top P low p hsig hbound hbranch hn
    t s hpt htp k ((markedGardenGraft sig top P (fun B => (low B).garden) hsig).extendTime s τ)
  have ht := graftTimeSplit_extendTime_top sig top P (fun B => (low B).garden) hsig hf s τ
  have hl := graftTimeSplit_extendTime_lower sig top P (fun B => (low B).garden) hsig hf s τ
  have htf := congrArg ((ForestTimeDomain top p t).indicator
    (forestPhaseProd L γ δ sig top (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a)))) ht
  have hlf := congrArg (lowerPhaseIndicatorProduct L γ δ low p s
    (fun B a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a))) hl
  exact hi.trans (congrArg₂ (· * ·) htf hlf)

end WaveTurbulence.Induct
