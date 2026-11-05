/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftExpansionSums
public import WaveTurbulence.Foundations.XChain.LowerFamilyKernelSum
public import WaveTurbulence.Foundations.XChain.CanonicalCoupleGraft
/-! The exact top-tree kernel expansion for the source truncated couple class. -/
public section
namespace WaveTurbulence.Induct
open Finset
open SysAPI
open scoped Classical

theorem sum_graftExpansionData_eq_source_couple (p Ntop Natt : ℕ) (f : LayeredGarden 2 → ℂ) :
    (∑ D : GraftExpansionData ![1, -1] p Ntop Natt, f D.toCanonical.graft) =
      ∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p Ntop Natt}, f LG.1 := by
  have he := finsum_comp_equiv ((graftExpansionDataEquiv (p := p) ![1, -1] Ntop Natt).trans
    (canonicalCoupleGraftTruncEquiv p Ntop Natt)) (f := fun LG => f LG.1)
  exact (finsum_eq_sum_of_fintype
    (fun D : GraftExpansionData ![1, -1] p Ntop Natt => f D.toCanonical.graft)).symm.trans he

theorem couple_truncated_kernel_sum_eq_tree_expansion {d p : ℕ} (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (Ntop Natt : ℕ)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin 2 → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) :
    (∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧ LG.IsTrunc p Ntop Natt},
      KG L γ δ F LG.1 t n) =
    ∑ top : Fin 2 → TrTree Ntop,
      (∏ j, zpowSign (![1, -1] j) (treePrefactor L γ δ d (top j).1)) *
      ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
          TopPartitionIrreducible (fun j => (top j).1) P},
        ∑' κ : ForestDecoration (fun j => (top j).1) d n,
          (∏ j, topTreeCoefficient L γ δ p (fun j => (top j).1) ![1, -1] n κ (fun _ => t) j) *
          ∏ B : P.1.parts, lowerKernelSum L γ δ F
            (fun k => nodeSign ![1, -1] ((blockRootEquiv (fun j => (top j).1) P.1).symm ⟨B, k⟩).1) p Natt
            (fun k => κ.1 ((blockRootEquiv (fun j => (top j).1) P.1).symm ⟨B, k⟩).toNode) := by
  rw [← sum_graftExpansionData_eq_source_couple p Ntop Natt (fun LG => KG L γ δ F LG t n)]
  rw [sum_graftExpansionData_eq_index ![1, -1] Ntop Natt]
  apply sum_congr rfl
  intro top _
  rw [mul_sum]
  apply sum_congr rfl
  intro P _
  exact sum_KG_graftLowerFamily L γ δ F ![1, -1] (fun j => (top j).1) P.1 P.2 t hpt htp n hF

end WaveTurbulence.Induct
