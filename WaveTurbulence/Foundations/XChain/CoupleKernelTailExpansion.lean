/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CoupleOrderKernelExpansion
public import WaveTurbulence.Foundations.XChain.GraftExpansionSums
public import WaveTurbulence.Foundations.XChain.LowerFamilyOrderKernel
public import WaveTurbulence.Foundations.XChain.LowerOrderTail
/-! The actual total-order weighted canonical-garden sum has an exact independently grouped expansion. -/
public section
namespace WaveTurbulence.Induct
open Finset
open SysAPI
open scoped Classical

theorem couple_truncated_kernel_tail_eq_order_tail {d p : ℕ} (L γ δ : ℝ)
    (F : ℕ → Mom d → ℝ) (Ntop Natt : ℕ)
    (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1) (n : Fin 2 → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) (Ncut : ℕ) :
    (∑ᶠ LG : {LG : LayeredGarden 2 // IsCanonC (p + 1) LG ∧
      LG.IsTrunc p Ntop Natt}, if Ncut < LG.1.garden.order then KG L γ δ F LG.1 t n else 0) =
    ∑ top : Fin 2 → TrTree Ntop,
      (∏ j, zpowSign (![1, -1] j) (treePrefactor L γ δ d (top j).1)) *
      ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
          TopPartitionIrreducible (fun j => (top j).1) P},
        lowerOrderTail L γ δ F ![1, -1] (fun j => (top j).1) P.1 p Natt
          ((Ncut + 1) - ∑ j, (top j).1.order) t n := by
  classical
  have he := couple_truncated_weighted_kernel_sum_eq_order_expansion L γ δ F Ntop Natt
    t hpt htp n hF (fun N => if Ncut < N then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at he
  refine he.trans ?_
  apply sum_congr rfl
  intro top _
  apply congrArg (fun z : ℂ => (∏ j, zpowSign (![1, -1] j) (treePrefactor L γ δ d (top j).1)) * z)
  apply sum_congr rfl
  intro P _
  unfold lowerOrderTail lowerOrderTailIntegrand
  apply tsum_congr
  intro κ
  apply congrArg (fun z : ℂ => (∏ j, topTreeCoefficient L γ δ p (fun j => (top j).1) ![1, -1] n κ (fun _ => t) j) * z)
  apply sum_congr rfl
  intro orders _
  have hiff : (Ncut < (∑ j, (top j).1.order) + ∑ B, (orders B).1) ↔
      (Ncut + 1) - (∑ j, (top j).1.order) ≤ ∑ B, (orders B).1 := by omega
  by_cases h : Ncut < (∑ j, (top j).1.order) + ∑ B, (orders B).1
  · exact (ite_eq_left h).trans (ite_eq_left (hiff.mp h)).symm
  · exact (ite_eq_right h).trans (ite_eq_right (fun hh => h (hiff.mpr hh))).symm

end WaveTurbulence.Induct
