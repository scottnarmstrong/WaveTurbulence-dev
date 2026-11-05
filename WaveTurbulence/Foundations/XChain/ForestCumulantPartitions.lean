/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestCumulantSeries
public import WaveTurbulence.Foundations.XChain.ForestPartitionConvergence
/-! The exact top-tree cumulant expansion with each irreducible leaf partition isolated. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open SysAPI
open scoped ENNReal Classical

theorem cumulant_forest_eq_sum_leaf_partitions {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {w d : ℕ} (L γ δ : ℝ) (p : ℕ) (top : Fin w → TTree)
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (t : Fin w → ℝ) (n : Fin w → (Fin d → ℤ)) (sig : Fin w → ℤˣ) :
    cumulant μ (fun j ω => zpowSign (sig j) (treeTerm L γ δ p (top j) (c ω) (t j) (n j))) univ =
      (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j))) *
      ∑ P ∈ (univ : Finset (Finpartition (univ : Finset (GLeaf top)))).filter
          (TopPartitionIrreducible top),
        ∑' κ : ForestDecoration top d n, (∏ j, topTreeCoefficient L γ δ p top sig n κ t j) *
          ∏ B ∈ P.parts, cumulant μ (fun l ω => zpowSign (nodeSign sig l.1) (c ω (κ.1 l.toNode))) B := by
  rw [cumulant_forest_eq_leaf_partition_series L γ δ p top c hc hcs hM t n sig]
  apply congrArg (fun z : ℂ => (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j))) * z)
  simp_rw [mul_sum]
  exact Summable.tsum_finsetSum (fun P _ =>
    summable_forest_partition_contribution L γ δ p top n sig t c hc hcs hM P)

end WaveTurbulence.Induct
