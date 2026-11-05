/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftFreePhaseIndicator
public import WaveTurbulence.Foundations.XChain.GraftPhaseIndicator
public import WaveTurbulence.Foundations.XChain.GraftLowerTimeIntegrals
public import WaveTurbulence.Foundations.XChain.UnmarkedPhaseIntegral
/-! Integrated phase factorization with arbitrary signed top trees and retained flower leaves. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open scoped Classical

theorem phaseIntegral_graft {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (hf : ∀ B b, ¬ (low B).garden.IsFlowerParent b)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (k : GNode (graftForest top (blockGraftTrees top P (fun B => (low B).garden))) → Mom d) :
    phaseIntegral L γ δ (markedLayeredGardenGraft sig top P low p hsig hbound).garden
      (kDomain (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) s) s k =
    graftTopPhaseIntegral L γ δ sig top P (fun B => (low B).garden) hsig
      (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a)) p t s *
    ∏ B : P.parts, phaseIntegral L γ δ (low B).garden (kDomain (low B) (fun _ => p) s) s
      (fun a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a)) := by
  let f := graftTopPhaseFn L γ δ sig top P (fun B => (low B).garden) hsig
    (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a)) p t s
  let gl := fun B => (kDomain (low B) (fun _ => p) s).indicator (phaseProd L γ δ (low B).garden
    (fun a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a)))
  let g := lowerPhaseIndicatorProduct L γ δ low p s
    (fun B a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a))
  have hi := integral_congr_ae
    (μ := (volume : Measure ((markedGardenGraft sig top P (fun B => (low B).garden) hsig).FreeBranch → ℝ)))
    (ae_of_all _ (phaseIndicator_freeGraft L γ δ sig top P low p hsig hbound hbranch hn hf t s hpt htp k))
  have hs := ((measurePreserving_graftFlowerFreeTimeSplit sig top P (fun B => (low B).garden) hsig hf).integral_comp'
    (fun z => f z.1 * g z.2)).trans (integral_prod_mul f g)
  have hl := integral_lowerTime_prod top P (fun B => (low B).garden) gl
  have hp := Finset.prod_congr (s₁ := (univ : Finset P.parts)) rfl (fun B _ =>
    (phaseIntegral_of_no_flowerParent L γ δ (low B).garden (hf B)
      (kDomain (low B) (fun _ => p) s) s
      (fun a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a))).symm)
  exact hi.trans (hs.trans ((congrArg (fun z : ℂ => (∫ τ, f τ) * z) hl).trans
    (congrArg (fun z : ℂ => (∫ τ, f τ) * z) hp)))

end WaveTurbulence.Induct
