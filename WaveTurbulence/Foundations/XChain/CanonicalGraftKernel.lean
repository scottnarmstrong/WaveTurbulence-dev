/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGraftTruncEquiv
public import WaveTurbulence.Foundations.XChain.GraftKernelComponents
public import WaveTurbulence.Foundations.XChain.PlainGraftEquality
/-! The generic kernel/time factorization specialized to the actual canonical construction. -/
public section
namespace WaveTurbulence.Induct
open Finset

namespace CanonicalGraftData

theorem lower_branch_layer_lt {w p : ℕ} {sig : Fin w → ℤˣ} (C : CanonicalGraftData sig p)
    (B : C.partition.parts) (b : GBranch (C.low B).garden.tree) : (C.low B).layer b.toNode < p := by
  rcases C.component B with hc | hp
  · exact isCanonG_layer_lt hc b.toNode
  · have hb := b.2
    rw [hp.2.1 b.1.1, TTree.branching] at hb
    exact False.elim (notMem_empty _ hb)

theorem kernel_graft {d w p : ℕ} {sig : Fin w → ℤˣ} (C : CanonicalGraftData sig p)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (t : ℝ)
    (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (k₀ : Mom d) (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (k₀ + latticePoint L m)|) :
    kernelK L γ δ F C.graft (fun _ => t) 0 k₀ n 0 =
    ((coupling d L γ δ : ℂ) ^ (∑ j, (C.top j).order) *
      ∏ b : GBranch C.top, Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ)) *
    ∑' kt : ForestDecoration C.top d n,
      topDecorationFactor L γ δ sig C.top C.partition (fun B => (C.low B).garden) C.sign kt.1 k₀ p t 0 *
      ∏ B : C.partition.parts, kernelK L γ δ F (C.low B) (fun _ => p) 0 k₀
        (fun k => kt.1 ((blockRootEquiv C.top C.partition).symm ⟨B, k⟩).toNode) 0 := by
  have he := markedLayeredGardenGraft_eq_layeredGardenGraft sig C.top C.partition C.low p
    C.plain C.sign C.layer_bound
  have hn : ∀ B l, (C.low B).garden.mark l ≠ some MarkTag.lower := by
    intro B l h
    have hf := (C.plain B l).symm.trans h
    cases hf
  have hk := kernelK_graft L γ δ F sig C.top C.partition C.low p C.sign C.layer_bound
    C.lower_branch_layer_lt hn (fun B => not_flowerParent_of_plain _ (C.plain B))
    t 0 hpt htp k₀ n 0 hF
  exact (congrArg (fun LG : LayeredGarden w => kernelK L γ δ F LG (fun _ => t) 0 k₀ n 0) he).symm.trans hk

end CanonicalGraftData
end WaveTurbulence.Induct
