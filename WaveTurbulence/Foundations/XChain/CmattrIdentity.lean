/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CmattrError
public import WaveTurbulence.Foundations.XChain.TruncatedCumulantPartitionCarrier
public import WaveTurbulence.Foundations.XChain.CanonicalKernelExpansion
public import WaveTurbulence.Foundations.XChain.CoupleKernelExpansion
/-! T.cmattr: the literal truncated-tree cumulant is the full canonical kernel sum plus explicit input errors. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open SysAPI
open scoped ENNReal Classical

section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {w d : ℕ}
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ)
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (p Ntop Natt : ℕ) (t : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (n : Fin w → (Fin d → ℤ))
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|)
include hc hcs hM hpt htp hF

theorem cumulant_aTr_eq_kernelExpansion_add_error :
    cumulant μ (fun j ω => zpowSign (sig j) (aTr L γ δ p Ntop (c ω) t (n j))) univ =
      treeKernelExpansion L γ δ F sig p Ntop Natt t n + cmattrError μ L γ δ F sig c p Ntop Natt t n := by
  rw [cumulant_aTr_eq_partition_carrier L γ δ p Ntop c hc hcs hM t n sig]
  have he : (∑ top : Fin w → TrTree Ntop,
      (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j).1)) *
      ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
          TopPartitionIrreducible (fun j => (top j).1) P},
        ∑' κ : ForestDecoration (fun j => (top j).1) d n,
          topPartitionCumulantIntegrand μ L γ δ sig (fun j => (top j).1) P.1 c p t n κ) =
      ∑ top : Fin w → TrTree Ntop,
        (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j).1)) *
        ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
            TopPartitionIrreducible (fun j => (top j).1) P},
          ((∑' κ : ForestDecoration (fun j => (top j).1) d n,
            topPartitionKernelIntegrand L γ δ F sig (fun j => (top j).1) P.1 p Natt t n κ) +
            topPartitionError μ L γ δ F sig (fun j => (top j).1) P.1 c p Natt t n) := by
    apply sum_congr rfl
    intro top _
    apply congrArg (fun z : ℂ => (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j).1)) * z)
    apply sum_congr rfl
    intro P _
    exact topPartitionCumulant_eq_kernel_add_error L γ δ sig (fun j => (top j).1) P.1 c hc hcs hM
      p t n F Natt P.2 hpt htp hF
  exact he.trans (by simp only [treeKernelExpansion, cmattrError, sum_add_distrib, mul_add])

theorem cumulant_aTr_eq_canonG_sum_add_error (hw : 4 ≤ w) :
    cumulant μ (fun j ω => zpowSign (sig j) (aTr L γ δ p Ntop (c ω) t (n j))) univ =
      (∑ᶠ LG : {LG : LayeredGarden w // IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧
        LG.IsTrunc p Ntop Natt}, KG L γ δ F LG.1 t n) + cmattrError μ L γ δ F sig c p Ntop Natt t n := by
  have he := cumulant_aTr_eq_kernelExpansion_add_error L γ δ F sig c hc hcs hM p Ntop Natt t hpt htp n hF
  have hk : (∑ᶠ LG : {LG : LayeredGarden w // IsCanonG (p + 1) LG ∧ LG.garden.sig = sig ∧
      LG.IsTrunc p Ntop Natt}, KG L γ δ F LG.1 t n) = treeKernelExpansion L γ δ F sig p Ntop Natt t n :=
    canonical_truncated_kernel_sum_eq_tree_expansion L γ δ F sig hw Ntop Natt t hpt htp n hF
  exact he.trans (congrArg (fun z : ℂ => z + cmattrError μ L γ δ F sig c p Ntop Natt t n) hk.symm)

end
end WaveTurbulence.Induct
