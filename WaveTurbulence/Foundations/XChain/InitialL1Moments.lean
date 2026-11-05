/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GaussianMassMoments
public import WaveTurbulence.Foundations.Probability.RandomRapidDecay
/-! All finite moments of the initial absolute lattice sum, used in the base tree expansion. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem memLp_gaussian_norm (p : ℕ) :
    MemLp (fun z : ℂ => ‖z‖) (p : ℝ≥0∞) stdComplexGaussian := by
  have h := (memLp_id_stdComplexGaussian (p : ℝ≥0)).norm
  simpa only [ENNReal.coe_natCast, id_eq] using h

/-- The summably weighted Gaussian ℓ1 norm has every finite positive moment. -/
theorem memLp_initial_l1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} {L : ℝ} (hL : 0 < L) (φ : SchwartzMap (Mom d) ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) (hg : ∀ n, HasLaw (g n) stdComplexGaussian μ)
    (p : ℕ) (hp : 1 ≤ p) :
    MemLp (fun ω => ∑' n, ‖initialCoeff L φ g ω n‖) (p : ℝ≥0∞) μ := by
  have hsqrt : Summable fun n => Real.sqrt (φ (latticePoint L n)) := by
    have h := (Probability.isRapidDecay_sqrt_schwartz hL φ).summable_norm_mul_pow 0
    simpa only [pow_zero, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using h
  have h := memLp_gaussian_weighted_function g hg (by exact_mod_cast hp) (fun z : ℂ => ‖z‖)
    (memLp_gaussian_norm p) (fun n => Real.sqrt (φ (latticePoint L n))) (fun n => Real.sqrt_nonneg _) hsqrt
  simpa only [initialCoeff, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)] using h

end WaveTurbulence.Induct
