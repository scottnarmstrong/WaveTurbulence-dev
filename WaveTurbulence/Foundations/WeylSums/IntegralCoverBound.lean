/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Bounds from countable covers without disjointness -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- Summable nonnegative local integral bounds control the integral on a
countable cover. Overlap of the sets is harmless. -/
theorem integrable_integral_le_of_cover {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (s : ℕ → Set X)
    (hs : (⋃ n, s n) = Set.univ) (hi : ∀ n, IntegrableOn f (s n) μ)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hbs : Summable b)
    (hbound : ∀ n, (∫ x in s n, f x ∂μ) ≤ b n) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ ∑' n, b n := by
  have hnorm (n : ℕ) : (∫ x in s n, ‖f x‖ ∂μ) = ∫ x in s n, f x ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => Real.norm_of_nonneg (hf x))
  have hsum : Summable (fun n => ∫ x in s n, ‖f x‖ ∂μ) := by
    apply hbs.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
    intro n
    rw [hnorm]
    exact hbound n
  have hiAll : Integrable f μ := by
    have hh := integrableOn_iUnion_of_summable_integral_norm hi hsum
    rwa [hs, integrableOn_univ] at hh
  refine ⟨hiAll,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg hb)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hiAll (Filter.Eventually.of_forall hf),
    ENNReal.ofReal_tsum_of_nonneg hb hbs]
  calc
    _ = ∫⁻ x in ⋃ n, s n, ENNReal.ofReal (f x) ∂μ := by rw [hs, Measure.restrict_univ]
    _ ≤ ∑' n, ∫⁻ x in s n, ENNReal.ofReal (f x) ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' n, ENNReal.ofReal (b n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Filter.Eventually.of_forall hf)]
      exact ENNReal.ofReal_le_ofReal (hbound n)

end WaveTurbulence.WeylSums
