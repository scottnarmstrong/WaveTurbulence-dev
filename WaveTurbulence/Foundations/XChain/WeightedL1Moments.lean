/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestWeightedNormSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
/-! Deterministic summable spatial decay supplies every finite moment of the actual absolute lattice sum. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory
open scoped ENNReal

theorem memLp_l1_of_summable_weight {Ω β : Type*} [MeasurableSpace Ω] [Countable β]
    (μ : Measure Ω) [IsFiniteMeasure μ] (c : Ω → β → ℂ)
    (hc : ∀ n, Measurable (fun ω => c ω n)) (v : β → ℝ) (hv : Summable v)
    (hn : ∀ n, 0 ≤ v n) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂μ, ∀ n, ‖c ω n‖ ≤ C * v n) (p : ℝ≥0∞) :
    MemLp (fun ω => ∑' n, ‖c ω n‖) p μ := by
  have hs : ∀ᵐ ω ∂μ, Summable (fun n => ‖c ω n‖) := by
    filter_upwards [hb] with ω hω
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hω (hv.mul_left C)
  let f : Ω → ℝ := fun ω => (∑' n, ENNReal.ofReal ‖c ω n‖).toReal
  have hf : Measurable f := by
    exact (Measurable.ennreal_tsum (fun n => (hc n).norm.ennreal_ofReal)).ennreal_toReal
  have he : f =ᵐ[μ] fun ω => ∑' n, ‖c ω n‖ := by
    filter_upwards [hs] with ω hω
    dsimp [f]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) hω,
      ENNReal.toReal_ofReal (tsum_nonneg (fun n => norm_nonneg _))]
  apply MemLp.of_bound (hf.aestronglyMeasurable.congr he) (C * ∑' n, v n)
  filter_upwards [hs, hb] with ω hω hbound
  rw [Real.norm_of_nonneg (tsum_nonneg (fun n => norm_nonneg _))]
  have h := hω.tsum_le_tsum hbound (hv.mul_left C)
  simpa only [tsum_mul_left] using h

end WaveTurbulence.Induct
