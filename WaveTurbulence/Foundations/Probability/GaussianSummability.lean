/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Probability.GaussianEvents
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Almost-sure weighted summability of Gaussian families

A summable deterministic nonnegative envelope multiplied by Gaussian absolute
values is almost surely summable. Independence is unnecessary for this fact.
This is the probabilistic step of TARGET's smooth initial-data assertion.
-/

public section

namespace WaveTurbulence.Probability
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Any summable nonnegative deterministic weights remain summable after
multiplication by normalized Gaussian absolute values, almost surely. -/
theorem ae_summable_weighted_gaussian {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} [IsProbabilityMeasure P] (g : ι → Ω → ℂ)
    (hg : ∀ i, HasLaw (g i) stdComplexGaussian P)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsa : Summable a) :
    ∀ᵐ ω ∂P, Summable (fun i => a i * ‖g i ω‖) := by
  let f : ι → Ω → ℂ := fun i ω => (a i : ℂ) * g i ω
  have hgi (i : ι) : Integrable (g i) P := by
    simpa only [pow_one, pow_zero, mul_one] using
      integrable_monomial_of_hasLaw_stdComplexGaussian (hg i) 1 0
  have hfi (i : ι) : Integrable (f i) P := (hgi i).const_mul _
  have hn (i : ι) (ω : Ω) : ‖f i ω‖ = a i * ‖g i ω‖ := by
    simp only [f, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha i)]
  have heLp (i : ι) : eLpNorm (f i) 1 P ≤ ENNReal.ofReal (a i) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hfi i).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hfi i)]
    apply ENNReal.ofReal_le_ofReal
    simp_rw [hn]
    rw [integral_const_mul]
    exact mul_le_of_le_one_right (ha i) (integral_norm_le_one (hg i))
  have hsum : ∑' i, eLpNorm (f i) 1 P ≠ ⊤ :=
    ne_top_of_le_ne_top hsa.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum heLp)
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl hsum] with ω hω
  simpa only [hn] using hω

end WaveTurbulence.Probability
