/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.IrreduciblePartitionSums
public import WaveTurbulence.Foundations.XChain.ForestCumulantPartitions
public import WaveTurbulence.Foundations.XChain.TopPartitionSeries
/-! The actual top-tree cumulant uses exactly the same ordered partition carrier as the kernel expansion. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open SysAPI
open scoped ENNReal Classical

theorem cumulant_forest_eq_partition_carrier {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {w d : ℕ} (L γ δ : ℝ) (p : ℕ) (top : Fin w → TTree)
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (t : ℝ) (n : Fin w → (Fin d → ℤ)) (sig : Fin w → ℤˣ) :
    cumulant μ (fun j ω => zpowSign (sig j) (treeTerm L γ δ p (top j) (c ω) t (n j))) univ =
      (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j))) *
      ∑ P : {P : Finpartition (univ : Finset (GLeaf top)) // TopPartitionIrreducible top P},
        ∑' κ : ForestDecoration top d n, topPartitionCumulantIntegrand μ L γ δ sig top P.1 c p t n κ := by
  rw [cumulant_forest_eq_sum_leaf_partitions L γ δ p top c hc hcs hM (fun _ => t) n sig]
  apply congrArg (fun z : ℂ => (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j))) * z)
  refine Eq.trans ?_ (sum_irreducible_partitions top
    (fun P => ∑' κ : ForestDecoration top d n,
      topPartitionCumulantIntegrand μ L γ δ sig top P c p t n κ)).symm
  apply sum_congr rfl
  intro P _
  apply tsum_congr
  intro κ
  exact congrArg (fun z : ℂ => (∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j) * z)
    (prod_coe_sort P.parts (fun B => topBlockCumulant μ sig top c κ B)).symm

end WaveTurbulence.Induct
