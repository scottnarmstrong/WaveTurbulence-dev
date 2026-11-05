/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestPhaseIntegral
/-! Exact factorization of the kernel's time-domain indicator and phase. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem phaseIndicator_markedGraft {d w : ℕ} (L γ δ : ℝ) (sig : Fin w → ℤˣ)
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (k : GNode (graftForest top (blockGraftTrees top P (fun B => (low B).garden))) → Mom d)
    (τ : GBranch (graftForest top (blockGraftTrees top P (fun B => (low B).garden))) → ℝ) :
    (kDomain (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) s).indicator
      (phaseProd L γ δ (markedLayeredGardenGraft sig top P low p hsig hbound).garden k) τ =
    (ForestTimeDomain top p t).indicator
      (forestPhaseProd L γ δ sig top (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a)))
      (graftTimeSplit top P (fun B => (low B).garden) τ).1 *
    ∏ B : P.parts, (kDomain (low B) (fun _ => p) s).indicator
      (phaseProd L γ δ (low B).garden
        (fun a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a)))
      (fun b => (graftTimeSplit top P (fun B => (low B).garden) τ).2 ⟨B, b⟩) := by
  classical
  let big := markedLayeredGardenGraft sig top P low p hsig hbound
  let tt := (graftTimeSplit top P (fun B => (low B).garden) τ).1
  let tl := (graftTimeSplit top P (fun B => (low B).garden) τ).2
  let f := forestPhaseProd L γ δ sig top
    (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a)) tt
  let g := fun B => phaseProd L γ δ (low B).garden
    (fun a => k (lowerNodeEmbedding top P (fun B => (low B).garden) B a)) (fun b => tl ⟨B, b⟩)
  have hp := markedGardenGraft_phaseProd_eq_forest L γ δ sig top P
    (fun B => (low B).garden) hsig k τ
  have hd := kDomain_markedGraft_iff sig top P low p hsig hbound hbranch hn t s hpt htp τ
  have hv := congrArg (fun z : ℂ => if τ ∈ kDomain big (fun _ => t) s then z else 0) hp
  have hc : (if τ ∈ kDomain big (fun _ => t) s then f * ∏ B, g B else 0) =
      (if tt ∈ ForestTimeDomain top p t ∧
          ∀ B, (fun b => tl ⟨B, b⟩) ∈ kDomain (low B) (fun _ => p) s
        then f * ∏ B, g B else 0) := by
    by_cases hh : τ ∈ kDomain big (fun _ => t) s
    · rw [ite_eq_left hh, ite_eq_left (hd.mp hh)]
    · rw [ite_eq_right hh, ite_eq_right (fun h => hh (hd.mpr h))]
  exact hv.trans (hc.trans (ite_and_forall_mul_prod (tt ∈ ForestTimeDomain top p t)
    (fun B => (fun b => tl ⟨B, b⟩) ∈ kDomain (low B) (fun _ => p) s) f g))

end WaveTurbulence.Induct
