/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGraftKernel
public import WaveTurbulence.Foundations.XChain.ForestRootPrefactor
public import WaveTurbulence.Foundations.XChain.PlainTopCoefficient
/-! Canonical graft kernels in precisely the analytic tree-expansion coordinates of T.cmattr. -/
public section
namespace WaveTurbulence.Induct
open Finset
open SysAPI

namespace CanonicalGraftData

theorem KG_graft {d w p : ℕ} {sig : Fin w → ℤˣ} (C : CanonicalGraftData sig p)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (t : ℝ)
    (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) :
    KG L γ δ F C.graft t n =
      (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (C.top j))) *
      ∑' κ : ForestDecoration C.top d n,
        (∏ j, topTreeCoefficient L γ δ p C.top sig n κ (fun _ => t) j) *
        ∏ B : C.partition.parts, KG L γ δ F (C.low B) p
          (fun k => κ.1 ((blockRootEquiv C.top C.partition).symm ⟨B, k⟩).toNode) := by
  have hF' : ∀ q, Summable fun m : Fin d → ℤ => |F q ((0 : Mom d) + latticePoint L m)| := by
    simpa only [zero_add] using hF
  have hk := C.kernel_graft L γ δ F t hpt htp 0 n hF'
  have hp := prod_signed_treePrefactor_eq (d := d) L γ δ C.top sig
  have he : (∑' κ : ForestDecoration C.top d n,
      topDecorationFactor L γ δ sig C.top C.partition (fun B => (C.low B).garden) C.sign κ.1 0 p t 0 *
        ∏ B : C.partition.parts, kernelK L γ δ F (C.low B) (fun _ => p) 0 0
          (fun k => κ.1 ((blockRootEquiv C.top C.partition).symm ⟨B, k⟩).toNode) 0) =
      ∑' κ : ForestDecoration C.top d n,
        (∏ j, topTreeCoefficient L γ δ p C.top sig n κ (fun _ => t) j) *
        ∏ B : C.partition.parts, KG L γ δ F (C.low B) p
          (fun k => κ.1 ((blockRootEquiv C.top C.partition).symm ⟨B, k⟩).toNode) := by
    apply tsum_congr
    intro κ
    exact congrArg (fun z : ℂ => z * ∏ B : C.partition.parts, KG L γ δ F (C.low B) p
      (fun k => κ.1 ((blockRootEquiv C.top C.partition).symm ⟨B, k⟩).toNode))
      (topDecorationFactor_eq_prod_treeCoefficients L γ δ sig C.top C.partition
        (fun B => (C.low B).garden) C.sign C.plain n κ p t 0)
  exact hk.trans ((congrArg₂ (fun a b : ℂ => a * b) hp.symm he))

end CanonicalGraftData
end WaveTurbulence.Induct
