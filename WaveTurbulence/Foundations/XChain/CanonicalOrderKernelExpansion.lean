/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftExpansionSums
public import WaveTurbulence.Foundations.XChain.LowerFamilyOrderKernel
/-! The actual total-order weighted canonical-garden sum has an exact independently grouped expansion. -/
public section
namespace WaveTurbulence.Induct
open Finset
open SysAPI
open scoped Classical

theorem canonical_truncated_weighted_kernel_sum_eq_order_expansion {d w p : ℕ} (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ) (hw : 4 ≤ w) (Ntop Natt : ℕ)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) (W : ℕ → ℂ) :
    (∑ᶠ LG : {LG : LayeredGarden w // IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧
      LG.IsTrunc p Ntop Natt}, W LG.1.garden.order * KG L γ δ F LG.1 t n) =
    ∑ top : Fin w → TrTree Ntop,
      (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j).1)) *
      ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
          TopPartitionIrreducible (fun j => (top j).1) P},
        ∑' κ : ForestDecoration (fun j => (top j).1) d n,
          (∏ j, topTreeCoefficient L γ δ p (fun j => (top j).1) sig n κ (fun _ => t) j) *
          ∑ orders : P.1.parts → Fin (Natt + 1),
            W ((∑ j, (top j).1.order) + ∑ B, (orders B).1) *
              ∏ B : P.1.parts, lowerOrderKernelSum L γ δ F
                (fun k => nodeSign sig ((blockRootEquiv (fun j => (top j).1) P.1).symm ⟨B, k⟩).1) p Natt (orders B)
                (fun k => κ.1 ((blockRootEquiv (fun j => (top j).1) P.1).symm ⟨B, k⟩).toNode) := by
  rw [← sum_graftExpansionData_eq_source sig hw Ntop Natt (fun LG => W LG.garden.order * KG L γ δ F LG t n)]
  rw [sum_graftExpansionData_eq_index sig Ntop Natt]
  apply sum_congr rfl
  intro top _
  rw [mul_sum]
  apply sum_congr rfl
  intro P _
  exact sum_KG_graftLowerFamily_by_order L γ δ F sig (fun j => (top j).1) P.1 P.2 t hpt htp n hF W

end WaveTurbulence.Induct
