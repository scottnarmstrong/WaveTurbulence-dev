/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftKernelFactorization
public import WaveTurbulence.Foundations.XChain.GraftDecorationSums
/-! Exact kernelK sum reindexing for arbitrary top trees, including retained flower leaves. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem kernelK_graft_eq_tsum_boundary {d w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (hf : ∀ B b, ¬ (low B).garden.IsFlowerParent b)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelK L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) s k₀ n nfl =
    (coupling d L γ δ : ℂ) ^ (markedGardenGraft sig top P (fun B => (low B).garden) hsig).order *
      (markedGardenGraft sig top P (fun B => (low B).garden) hsig).zeta *
      ∑' x : BoundaryDecorationData top P (fun B => (low B).garden) d n nfl,
        topDecorationFactor L γ δ sig top P (fun B => (low B).garden) hsig x.1.1 k₀ p t s *
          ∏ B : P.parts, kernelDecorationFactor L γ δ F (low B) (fun _ => p) s k₀ (x.2 B) := by
  let big := markedLayeredGardenGraft sig top P low p hsig hbound
  let H := fun x : BoundaryDecorationData top P (fun B => (low B).garden) d n nfl =>
    topDecorationFactor L γ δ sig top P (fun B => (low B).garden) hsig x.1.1 k₀ p t s *
      ∏ B : P.parts, kernelDecorationFactor L γ δ F (low B) (fun _ => p) s k₀ (x.2 B)
  have hr := tsum_graftGenDecoration sig top P (fun B => (low B).garden) hsig n nfl
    (kernelDecorationFactor L γ δ F big (fun _ => t) s k₀)
  have hfactors (x : BoundaryDecorationData top P (fun B => (low B).garden) d n nfl) :
      kernelDecorationFactor L γ δ F big (fun _ => t) s k₀
        (assembleGenDecoration sig top P (fun B => (low B).garden) hsig n nfl x) = H x := by
    have he := kernelDecorationFactor_graft L γ δ F sig top P low p hsig hbound hbranch hn hf
      t s hpt htp k₀ n nfl (assembleGenDecoration sig top P (fun B => (low B).garden) hsig n nfl x)
    exact he.trans (congrArg H
      (split_assembleGenDecoration sig top P (fun B => (low B).garden) hsig n nfl x))
  have hs := hr.trans (tsum_congr hfactors)
  exact congrArg (fun z : ℂ => (coupling d L γ δ : ℂ) ^ big.garden.order * big.garden.zeta * z) hs

end WaveTurbulence.Induct
