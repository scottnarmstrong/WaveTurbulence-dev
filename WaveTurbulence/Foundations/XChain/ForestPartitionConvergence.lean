/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LeafPartitionSummability
public import WaveTurbulence.Foundations.XChain.TopCoefficientBounds
/-! Each source partition term including its actual top-tree coefficient is absolutely convergent. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open scoped ENNReal

theorem summable_forest_partition_contribution {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {w d : ℕ} (L γ δ : ℝ) (p : ℕ) (top : Fin w → TTree)
    (n : Fin w → (Fin d → ℤ)) (sig : Fin w → ℤˣ) (t : Fin w → ℝ)
    (c : Ω → (Fin d → ℤ) → ℂ)
    (hc : ∀ n, ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => c ω n) (q : ℝ≥0∞) μ)
    (hcs : ∀ᵐ ω ∂μ, Summable fun n => ‖c ω n‖)
    (hM : ∀ q : ℕ, 1 ≤ q → MemLp (fun ω => ∑' n, ‖c ω n‖) (q : ℝ≥0∞) μ)
    (P : Finpartition (univ : Finset (GLeaf top))) :
    Summable (fun κ : ForestDecoration top d n =>
      (∏ j, topTreeCoefficient L γ δ p top sig n κ t j) *
        ∏ B ∈ P.parts, cumulant μ (fun l ω => zpowSign (nodeSign sig l.1) (c ω (κ.1 l.toNode))) B) := by
  have hs := summable_leaf_partition_cumulants top n (fun l => nodeSign sig l.1) c hc hcs hM P
  apply (hs.norm.mul_left (∏ j, SysAPI.boxVol (top j) p (t j))).of_norm_bounded
  intro κ
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_prod_topTreeCoefficient_le L γ δ p top sig n κ t) (norm_nonneg _)

end WaveTurbulence.Induct
