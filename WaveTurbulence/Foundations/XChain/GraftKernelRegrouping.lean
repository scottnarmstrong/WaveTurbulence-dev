/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftBoundarySummability
public import WaveTurbulence.Foundations.XChain.IndependentDecorationSums
public import WaveTurbulence.Foundations.XChain.CountableDecorations
/-! Absolute convergence permits the graft kernel sum to be grouped by top decorations. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem kernelK_graft_eq_tsum_top_factors {d w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (hf : ∀ B b, ¬ (low B).garden.IsFlowerParent b)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (k₀ + latticePoint L m)|) :
    kernelK L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) s k₀ n nfl =
    (coupling d L γ δ : ℂ) ^ (markedGardenGraft sig top P (fun B => (low B).garden) hsig).order *
      (markedGardenGraft sig top P (fun B => (low B).garden) hsig).zeta *
      ∑' kt : ForestDecoration top d n,
        topDecorationFactor L γ δ sig top P (fun B => (low B).garden) hsig kt.1 k₀ p t s *
          ∏ B : P.parts, ∑' kl : GenDecoration (low B).garden d
            (fun k => kt.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) nfl,
              kernelDecorationFactor L γ δ F (low B) (fun _ => p) s k₀ kl := by
  have hs := summable_boundaryKernelFactor L γ δ F sig top P low p hsig hbound hbranch hn hf
    t s hpt htp k₀ n nfl hF
  have hsum := tsum_sigma_independent_prod
    (fun kt : ForestDecoration top d n =>
      topDecorationFactor L γ δ sig top P (fun B => (low B).garden) hsig kt.1 k₀ p t s)
    (fun (kt : ForestDecoration top d n) B
      (kl : GenDecoration (low B).garden d
        (fun k => kt.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) nfl) =>
      kernelDecorationFactor L γ δ F (low B) (fun _ => p) s k₀ kl) hs
  exact (kernelK_graft_eq_tsum_boundary L γ δ F sig top P low p hsig hbound hbranch hn hf
    t s hpt htp k₀ n nfl).trans
    (congrArg (fun z : ℂ => (coupling d L γ δ : ℂ) ^
      (markedGardenGraft sig top P (fun B => (low B).garden) hsig).order *
      (markedGardenGraft sig top P (fun B => (low B).garden) hsig).zeta * z) hsum)

end WaveTurbulence.Induct
