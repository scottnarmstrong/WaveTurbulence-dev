/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftBoundaryKernelFactor
public import WaveTurbulence.Foundations.XChain.GraftKernelSummability
/-! Source summability transported to the boundary factorization. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem summable_boundaryKernelFactor {d w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
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
    Summable (boundaryKernelFactor L γ δ F sig top P low hsig k₀ p t s (n := n) (nfl := nfl)) := by
  have hraw := summable_kernelDecorationFactor L γ δ F
    (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) s k₀ n nfl
    (markedLayeredGardenGraft_no_lone sig top P low p hsig hbound hn) hF
  have hr : Summable (fun x : BoundaryDecorationData top P (fun B => (low B).garden) d n nfl =>
      kernelDecorationFactor L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) s k₀
        (assembleGenDecoration sig top P (fun B => (low B).garden) hsig n nfl x)) :=
    (summable_assembleGenDecoration_iff sig top P (fun B => (low B).garden) hsig n nfl
      (kernelDecorationFactor L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound)
        (fun _ => t) s k₀)).mpr hraw
  exact hr.congr (kernelDecorationFactor_assemble L γ δ F sig top P low p hsig hbound hbranch hn hf
    t s hpt htp k₀ n nfl)

end WaveTurbulence.Induct
