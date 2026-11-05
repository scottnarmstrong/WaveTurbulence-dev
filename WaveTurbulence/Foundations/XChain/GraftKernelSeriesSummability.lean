/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftKernelComponents
/-! Absolute convergence of the top-decoration series with full lower kernels already grouped. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem summable_graft_kernel_series {d w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B l, (low B).garden.mark l ≠ some MarkTag.lower)
    (hf : ∀ B b, ¬ (low B).garden.IsFlowerParent b)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (k₀ + latticePoint L m)|) :
    Summable (fun kt : ForestDecoration top d n =>
      topDecorationFactor L γ δ sig top P (fun B => (low B).garden) hsig kt.1 k₀ p t s *
        ∏ B : P.parts, kernelK L γ δ F (low B) (fun _ => p) s k₀
          (fun k => kt.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) nfl) := by
  have hs := summable_boundaryKernelFactor L γ δ F sig top P low p hsig hbound hbranch hn hf
    t s hpt htp k₀ n nfl hF
  have hg := hs.sigma.mul_left (∏ B : P.parts,
    (coupling d L γ δ : ℂ) ^ (low B).garden.order * (low B).garden.zeta)
  apply hg.congr
  intro kt
  simp only [boundaryKernelFactor, tsum_mul_left, tsum_independent_prod,
    kernelK_eq_tsum_factors, prod_mul_distrib]
  ring

end WaveTurbulence.Induct
