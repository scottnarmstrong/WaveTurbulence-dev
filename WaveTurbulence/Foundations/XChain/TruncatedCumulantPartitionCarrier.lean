/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeCumulantPartitionCarrier
public import WaveTurbulence.Foundations.XChain.TruncatedTreeExpansion
public import WaveTurbulence.Foundations.XChain.TreeRandomMoments
/-! The literal truncated-tree cumulant on the source bounded-top-tree partition carrier. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open SysAPI
open scoped ENNReal Classical

theorem cumulant_aTr_eq_partition_carrier {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {w d : ℕ} (L γ δ : ℝ) (p Ntop : ℕ)
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (t : ℝ) (n : Fin w → (Fin d → ℤ)) (sig : Fin w → ℤˣ) :
    cumulant μ (fun j ω => zpowSign (sig j) (aTr L γ δ p Ntop (c ω) t (n j))) univ =
      ∑ top : Fin w → TrTree Ntop,
        (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j).1)) *
        ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
            TopPartitionIrreducible (fun j => (top j).1) P},
          ∑' κ : ForestDecoration (fun j => (top j).1) d n,
            topPartitionCumulantIntegrand μ L γ δ sig (fun j => (top j).1) P.1 c p t n κ := by
  have hcm (n : Fin d → ℤ) : AEStronglyMeasurable (fun ω => c ω n) μ :=
    (hc n 1 (by omega)).aestronglyMeasurable
  have hX (i : Fin w) (T : TrTree Ntop) (q : ℕ) (hq : 1 ≤ q) :=
    memLp_treeTerm L γ δ p T.1 c hcm hcs hM t (n i) q hq
  rw [cumulant_aTr_eq_sum_forests μ L γ δ p Ntop c (fun _ => t) n sig hX]
  exact sum_congr rfl (fun top _ =>
    cumulant_forest_eq_partition_carrier L γ δ p (fun j => (top j).1) c hc hcs hM t n sig)

end WaveTurbulence.Induct
