/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGraftTreeKernel
public import WaveTurbulence.Foundations.XChain.GraftKernelSeriesSummability
/-! Convergence of the canonical kernel in precisely its analytic tree-expansion coordinates. -/
public section
namespace WaveTurbulence.Induct
open Finset

namespace CanonicalGraftData

theorem summable_KG_graft_series {d w p : ℕ} {sig : Fin w → ℤˣ} (C : CanonicalGraftData sig p)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (t : ℝ)
    (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) :
    Summable (fun κ : ForestDecoration C.top d n =>
      (∏ j, topTreeCoefficient L γ δ p C.top sig n κ (fun _ => t) j) *
        ∏ B : C.partition.parts, KG L γ δ F (C.low B) p
          (fun k => κ.1 ((blockRootEquiv C.top C.partition).symm ⟨B, k⟩).toNode)) := by
  have hF' : ∀ q, Summable fun m : Fin d → ℤ => |F q ((0 : Mom d) + latticePoint L m)| := by
    simpa only [zero_add] using hF
  have hn : ∀ B l, (C.low B).garden.mark l ≠ some MarkTag.lower := by
    intro B l he
    have hf := (C.plain B l).symm.trans he
    cases hf
  have hs := summable_graft_kernel_series L γ δ F sig C.top C.partition C.low p C.sign C.layer_bound
    C.lower_branch_layer_lt hn (fun B => not_flowerParent_of_plain _ (C.plain B))
    t 0 hpt htp 0 n 0 hF'
  apply hs.congr
  intro κ
  exact congrArg (fun z : ℂ => z * ∏ B : C.partition.parts, KG L γ δ F (C.low B) p
    (fun k => κ.1 ((blockRootEquiv C.top C.partition).symm ⟨B, k⟩).toNode))
    (topDecorationFactor_eq_prod_treeCoefficients L γ δ sig C.top C.partition
      (fun B => (C.low B).garden) C.sign C.plain n κ p t 0)

end CanonicalGraftData
end WaveTurbulence.Induct
