/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.RandomSeries
public import WaveTurbulence.Foundations.Probability.GaussianEvents
/-! Every finite moment of the Gaussian initial mass, without independence assumptions. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- A summably weighted family with the Gaussian law inherits any fixed Lp test-function bound. -/
theorem memLp_gaussian_weighted_function {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (g : ι → Ω → ℂ)
    (hg : ∀ i, HasLaw (g i) stdComplexGaussian μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (ψ : ℂ → ℝ) (hψ : MemLp ψ p stdComplexGaussian)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsa : Summable a) :
    MemLp (fun ω => ∑' i, a i * ψ (g i ω)) p μ := by
  apply memLp_weighted_tsum hp (fun i => ψ ∘ g i) (fun i => (hg i).memLp_comp hψ)
    a ha hsa hψ.eLpNorm_ne_top
  intro i
  have hm : AEStronglyMeasurable ψ (Measure.map (g i) μ) := by
    rw [(hg i).map_eq]
    exact hψ.aestronglyMeasurable
  exact le_of_eq (by rw [← eLpNorm_map_measure hm (hg i).aemeasurable, (hg i).map_eq])

/-- Every finite Lp exponent is available for the mass density of one complex Gaussian. -/
theorem memLp_gaussian_norm_sq (p : ℕ) :
    MemLp (fun z : ℂ => ‖z‖ ^ 2) (p : ℝ≥0∞) stdComplexGaussian := by
  have h := memLp_id_stdComplexGaussian ((p : ℝ≥0) * 2)
  have h' := h.norm_rpow_div 2
  simpa only [ENNReal.coe_natCast, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.toReal_ofNat,
    Real.rpow_two, id_eq, ENNReal.mul_div_cancel_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)] using h'

/-- All finite moments of the summably weighted initial mass exist. -/
theorem memLp_gaussian_mass {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (g : ι → Ω → ℂ)
    (hg : ∀ i, HasLaw (g i) stdComplexGaussian μ)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsa : Summable a) (p : ℕ) (hp : 1 ≤ p) :
    MemLp (fun ω => ∑' i, a i * ‖g i ω‖ ^ 2) (p : ℝ≥0∞) μ :=
  memLp_gaussian_weighted_function g hg (by exact_mod_cast hp) _ (memLp_gaussian_norm_sq p) a ha hsa

end WaveTurbulence.Induct
