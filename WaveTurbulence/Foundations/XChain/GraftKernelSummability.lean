/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftKernelSum
public import WaveTurbulence.Foundations.WaveB.Lemmas
/-! Absolute convergence needed to regroup the actual graft kernel sums. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem summable_kernelDecorationFactor {d w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hn : ∀ ℓ, LG.garden.mark ℓ ≠ some MarkTag.lower)
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (k₀ + latticePoint L m)|) :
    Summable (kernelDecorationFactor L γ δ F LG up s k₀ (n := n) (nfl := nfl)) := by
  have hc : ∀ j, (univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1 := by
    intro j
    have he : (univ.filter fun ℓ : GLeaf LG.garden.tree =>
        ℓ.1.1 = j ∧ LG.garden.IsLone ℓ) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro ℓ _ h
      exact hn ℓ h.2
    rw [he]
    exact Nat.zero_le _
  exact (summable_kernelK_summand L γ δ F LG up s k₀ n nfl hc
    (fun ℓ _ => hF (LG.layer ℓ.toNode))).of_norm

end WaveTurbulence.Induct
