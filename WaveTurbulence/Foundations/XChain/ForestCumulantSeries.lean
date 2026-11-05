/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TreeCumulantSeries
public import WaveTurbulence.Foundations.XChain.CumulantTreeLeafGroups
public import WaveTurbulence.Foundations.XChain.ForestSeriesLabels
public import WaveTurbulence.Foundations.XChain.CumulantLinear
/-! The literal top-tree cumulant equals the convergent irreducible leaf-cumulant forest series. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open SysAPI
open scoped ENNReal Classical

theorem cumulant_forest_eq_leaf_partition_series {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {w d : ℕ} (L γ δ : ℝ) (p : ℕ) (top : Fin w → TTree)
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (t : Fin w → ℝ) (n : Fin w → (Fin d → ℤ)) (sig : Fin w → ℤˣ) :
    cumulant μ (fun j ω => zpowSign (sig j) (treeTerm L γ δ p (top j) (c ω) (t j) (n j))) univ =
      (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j))) *
      ∑' κ : ForestDecoration top d n, (∏ j, topTreeCoefficient L γ δ p top sig n κ t j) *
        ∑ P ∈ (univ : Finset (Finpartition (univ : Finset (GLeaf top)))).filter
          (TopPartitionIrreducible top),
          ∏ B ∈ P.parts, cumulant μ (fun l ω => zpowSign (nodeSign sig l.1) (c ω (κ.1 l.toNode))) B := by
  rw [cumulant_treeTerms_eq_decoration_series L γ δ p top c hc hcs hM t n sig univ]
  apply congrArg (fun z : ℂ => (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j))) * z)
  let f : ForestDecoration top d n → ℂ := fun κ =>
    cumulant μ (fun j ω => zpowSign (sig j)
      (treeSummand L γ δ p (top j) (c ω) (t j) (n j) (forestDecorationEquiv top n κ j))) univ
  have he : (∑' a : (i : ↥(univ : Finset (Fin w))) → TreeDecoration (top i.1) d (n i.1),
      cumulant μ (assignedFamily
        (fun i κ ω => zpowSign (sig i) (treeSummand L γ δ p (top i) (c ω) (t i) (n i) κ)) univ a) univ) =
      ∑' κ, f κ := by
    have ha (a : (i : ↥(univ : Finset (Fin w))) → TreeDecoration (top i.1) d (n i.1)) :
        cumulant μ (assignedFamily
          (fun i κ ω => zpowSign (sig i) (treeSummand L γ δ p (top i) (c ω) (t i) (n i) κ)) univ a) univ =
        f (forestSeriesLabelEquiv top n a) := by
      apply cumulant_congr_on
      intro j _ ω
      dsimp only [assignedFamily, f]
      rw [dif_pos (mem_univ j), forestSeriesLabelEquiv_component]
    exact (tsum_congr ha).trans ((forestSeriesLabelEquiv top n).tsum_eq f)
  rw [he]
  exact tsum_congr (fun κ => cumulant_treeSummands_eq_irreduciblePartitions μ L γ δ p top sig n κ t c)

end WaveTurbulence.Induct
