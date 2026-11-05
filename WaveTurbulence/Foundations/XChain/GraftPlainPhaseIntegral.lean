/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftPhaseIndicator
public import WaveTurbulence.Foundations.XChain.UnmarkedPhaseIntegral
public import WaveTurbulence.Foundations.XChain.GraftLowerTimeIntegrals
/-! Exact integrated phase factorization for arbitrary top trees and plain lower components. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem markedGardenGraft_isPlain {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hplain : ∀ B, (low B).IsPlain) : (markedGardenGraft sig top P low hsig).IsPlain := by
  intro ℓ
  obtain ⟨⟨B, l⟩, rfl⟩ := (gardenLeafEquiv top P low).symm.surjective ℓ
  exact (markedGardenGraft_mark_lower sig top P low hsig B l).trans (hplain B l)

theorem phaseIntegral_graft_of_plain {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hplain : ∀ B, (low B).garden.IsPlain)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (k : GNode (graftForest top (blockGraftTrees top P (fun B => (low B).garden))) → Mom d) :
    phaseIntegral L γ δ (markedLayeredGardenGraft sig top P low p hsig hbound).garden
      (kDomain (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) s) s k =
    forestPhaseIntegral L γ δ sig top
      (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a)) p t *
    ∏ B : P.parts, phaseIntegral L γ δ (low B).garden (kDomain (low B) (fun _ => p) s) s
      (fun a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a)) := by
  let big := markedLayeredGardenGraft sig top P low p hsig hbound
  let f := (ForestTimeDomain top p t).indicator (forestPhaseProd L γ δ sig top
    (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a)))
  let g := fun B => (kDomain (low B) (fun _ => p) s).indicator (phaseProd L γ δ (low B).garden
    (fun a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a)))
  have hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower := by
    intro B ℓ he
    have hf := (hplain B ℓ).symm.trans he
    cases hf
  have he := phaseIntegral_of_plain L γ δ big.garden
    (markedGardenGraft_isPlain sig top P (fun B => (low B).garden) hsig hplain)
    (kDomain big (fun _ => t) s) s k
  have hi := integral_congr_ae
    (μ := (volume : Measure (GBranch (graftForest top
      (blockGraftTrees top P (fun B => (low B).garden))) → ℝ))) (ae_of_all _ (phaseIndicator_markedGraft L γ δ sig top P low p
    hsig hbound hbranch hn t s hpt htp k))
  have hsplit := integral_graftTimeSplit_mul top P (fun B => (low B).garden) f
    (fun τ => ∏ B, g B (fun b => τ ⟨B, b⟩))
  have hprod := integral_lowerTime_prod top P (fun B => (low B).garden) g
  have hp := Finset.prod_congr (s₁ := (univ : Finset P.parts)) rfl (fun B _ =>
    (phaseIntegral_of_plain L γ δ (low B).garden (hplain B)
      (kDomain (low B) (fun _ => p) s) s
      (fun a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a))).symm)
  exact he.trans (hi.trans (hsplit.trans
    ((congrArg (fun z : ℂ => (∫ τ, f τ) * z) hprod).trans
      (congrArg (fun z : ℂ => (∫ τ, f τ) * z) hp))))

end WaveTurbulence.Induct
