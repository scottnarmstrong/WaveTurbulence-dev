/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftKernelFactorization
/-! The literal kernel factor on the boundary-decoration carrier. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def boundaryKernelFactor {d w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (k₀ : Mom d) (p t s : ℝ) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (x : BoundaryDecorationData top P (fun B => (low B).garden) d n nfl) : ℂ :=
  topDecorationFactor L γ δ sig top P (fun B => (low B).garden) hsig x.1.1 k₀ p t s *
    ∏ B, kernelDecorationFactor L γ δ F (low B) (fun _ => p) s k₀ (x.2 B)

theorem kernelDecorationFactor_assemble {d w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (hf : ∀ B b, ¬ (low B).garden.IsFlowerParent b)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (x : BoundaryDecorationData top P (fun B => (low B).garden) d n nfl) :
    kernelDecorationFactor L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound)
      (fun _ => t) s k₀ (assembleGenDecoration sig top P (fun B => (low B).garden) hsig n nfl x) =
      boundaryKernelFactor L γ δ F sig top P low hsig k₀ p t s x := by
  have he := kernelDecorationFactor_graft L γ δ F sig top P low p hsig hbound hbranch hn hf
    t s hpt htp k₀ n nfl (assembleGenDecoration sig top P (fun B => (low B).garden) hsig n nfl x)
  exact he.trans (congrArg (boundaryKernelFactor L γ δ F sig top P low hsig k₀ p t s)
    (split_assembleGenDecoration sig top P (fun B => (low B).garden) hsig n nfl x))

end WaveTurbulence.Induct
