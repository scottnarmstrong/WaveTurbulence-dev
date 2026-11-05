/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopPartitionSeries
/-! The concrete T.cmattr error converges and gives an exact actual-cumulant/kernel decomposition. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open scoped ENNReal

section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {w d : ℕ}
    (L γ δ : ℝ) (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (p : ℕ) (t : ℝ) (n : Fin w → (Fin d → ℤ))

include hc hcs hM

theorem summable_topPartitionCumulantIntegrand :
    Summable (topPartitionCumulantIntegrand μ L γ δ sig top P c p t n) := by
  have hs := summable_forest_partition_contribution L γ δ p top n sig (fun _ => t) c hc hcs hM P
  apply hs.congr
  intro κ
  exact congrArg (fun z : ℂ => (∏ j, topTreeCoefficient L γ δ p top sig n κ (fun _ => t) j) * z)
    (prod_coe_sort P.parts (fun B => topBlockCumulant μ sig top c κ B)).symm

variable (F : ℕ → Mom d → ℝ) (Natt : ℕ) (hP : TopPartitionIrreducible top P)
    (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|)

include hP hpt htp hF

theorem summable_topPartitionErrorIntegrand :
    Summable (topPartitionErrorIntegrand μ L γ δ F sig top P c p Natt t n) := by
  have ha := summable_topPartitionCumulantIntegrand L γ δ sig top P c hc hcs hM p t n
  have hb : Summable (topPartitionKernelIntegrand L γ δ F sig top P p Natt t n) :=
    summable_lowerKernelSum_graft_series (p := p) (Natt := Natt) L γ δ F sig top P hP t hpt htp n hF
  apply (ha.sub hb).congr
  intro κ
  exact (topPartitionErrorIntegrand_eq_sub μ L γ δ F sig top P c p Natt t n κ).symm

theorem topPartitionCumulant_eq_kernel_add_error :
    (∑' κ : ForestDecoration top d n, topPartitionCumulantIntegrand μ L γ δ sig top P c p t n κ) =
      (∑' κ : ForestDecoration top d n, topPartitionKernelIntegrand L γ δ F sig top P p Natt t n κ) +
        topPartitionError μ L γ δ F sig top P c p Natt t n := by
  have ha := summable_topPartitionCumulantIntegrand L γ δ sig top P c hc hcs hM p t n
  have hb : Summable (topPartitionKernelIntegrand L γ δ F sig top P p Natt t n) :=
    summable_lowerKernelSum_graft_series (p := p) (Natt := Natt) L γ δ F sig top P hP t hpt htp n hF
  have he : topPartitionError μ L γ δ F sig top P c p Natt t n =
      (∑' κ : ForestDecoration top d n, topPartitionCumulantIntegrand μ L γ δ sig top P c p t n κ) -
        ∑' κ : ForestDecoration top d n, topPartitionKernelIntegrand L γ δ F sig top P p Natt t n κ := by
    exact (tsum_congr (fun κ => topPartitionErrorIntegrand_eq_sub μ L γ δ F sig top P c p Natt t n κ)).trans
      (ha.tsum_sub hb)
  exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)

end
end WaveTurbulence.Induct
