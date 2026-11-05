/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.WeightedL1Moments
/-! Actual solution decay from the truncated approximation and remainder gives the internal l1 invariant. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory
open scoped ENNReal

theorem norm_le_of_two_spatial_bounds {d : ℕ} (L A Λ C D : ℝ) (hΛA : Λ ≤ A)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (f y : (Fin d → ℤ) → ℂ)
    (hy : ∀ n, ‖y n‖ ≤ jbr (latticePoint L n) ^ (-A) * C)
    (he : ∀ n, ‖f n - y n‖ ≤ jbr (latticePoint L n) ^ (-Λ) * D) (n : Fin d → ℤ) :
    ‖f n‖ ≤ (C + D) * jbr (latticePoint L n) ^ (-Λ) := by
  have hw := Real.rpow_le_rpow_of_exponent_le (one_le_jbr (latticePoint L n)) (neg_le_neg hΛA)
  have h := (hy n).trans (mul_le_mul_of_nonneg_right hw hC)
  have ht : ‖f n‖ ≤ ‖y n‖ + ‖f n - y n‖ := by
    have hh := norm_add_le (y n) (f n - y n)
    have heq : y n + (f n - y n) = f n := by ring
    rw [heq] at hh
    exact hh
  nlinarith [he n]

theorem memLp_l1_of_two_spatial_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {d : ℕ} (L A Λ C D : ℝ)
    (hL : 1 ≤ L) (hΛ : (d : ℝ) + 1 ≤ Λ) (hΛA : Λ ≤ A)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (f y : Ω → (Fin d → ℤ) → ℂ)
    (hf : ∀ n, Measurable (fun ω => f ω n))
    (hy : ∀ᵐ ω ∂μ, ∀ n, ‖y ω n‖ ≤ jbr (latticePoint L n) ^ (-A) * C)
    (he : ∀ᵐ ω ∂μ, ∀ n, ‖f ω n - y ω n‖ ≤ jbr (latticePoint L n) ^ (-Λ) * D)
    (q : ℝ≥0∞) : MemLp (fun ω => ∑' n, ‖f ω n‖) q μ := by
  apply memLp_l1_of_summable_weight μ f hf (fun n => jbr (latticePoint L n) ^ (-Λ))
    (summable_lattice_bracket_weight L Λ hL hΛ)
    (fun n => Real.rpow_nonneg (jbr_pos _).le _) (C + D) (add_nonneg hC hD) _ q
  filter_upwards [hy, he] with ω hω hω'
  exact norm_le_of_two_spatial_bounds L A Λ C D hΛA hC hD (f ω) (y ω) hω hω'

end WaveTurbulence.Induct
