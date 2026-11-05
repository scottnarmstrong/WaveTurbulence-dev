/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CoupleKernelExpansion
public import WaveTurbulence.Foundations.XChain.LowerFamilyOrderKernel
/-! Actual total-order weights for the full truncated couple class. -/
public section
namespace WaveTurbulence.Induct
open Finset SysAPI
open scoped Classical

theorem couple_truncated_weighted_kernel_sum_eq_order_expansion {d p : ℕ} (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (Ntop Natt : ℕ)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin 2 → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) (W : ℕ → ℂ) :
    (∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p Ntop Natt},
      W LG.1.garden.order * KG L γ δ F LG.1 t n) =
    ∑ top : Fin 2 → TrTree Ntop,
      (∏ j, zpowSign (![1, -1] j) (treePrefactor L γ δ d (top j).1)) *
      ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
          TopPartitionIrreducible (fun j => (top j).1) P},
        ∑' κ : ForestDecoration (fun j => (top j).1) d n,
          (∏ j, topTreeCoefficient L γ δ p (fun j => (top j).1) ![1, -1] n κ (fun _ => t) j) *
          ∑ orders : P.1.parts → Fin (Natt + 1),
            W ((∑ j, (top j).1.order) + ∑ B, (orders B).1) *
              ∏ B : P.1.parts, lowerOrderKernelSum L γ δ F
                (fun k => nodeSign ![1, -1] ((blockRootEquiv (fun j => (top j).1) P.1).symm ⟨B, k⟩).1) p Natt (orders B)
                (fun k => κ.1 ((blockRootEquiv (fun j => (top j).1) P.1).symm ⟨B, k⟩).toNode) := by
  rw [← sum_graftExpansionData_eq_source_couple p Ntop Natt (fun LG => W LG.garden.order * KG L γ δ F LG t n)]
  rw [sum_graftExpansionData_eq_index ![1, -1] Ntop Natt]
  apply sum_congr rfl
  intro top _
  rw [mul_sum]
  apply sum_congr rfl
  intro P _
  exact sum_KG_graftLowerFamily_by_order L γ δ F ![1, -1] (fun j => (top j).1) P.1 P.2 t hpt htp n hF W

end WaveTurbulence.Induct
