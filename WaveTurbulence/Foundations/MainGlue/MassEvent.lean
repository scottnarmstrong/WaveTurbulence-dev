/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.MainGlue.GaussianLaw
public import WaveTurbulence.Foundations.Probability.GaussianEvents
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# G6: the initial mass on an arbitrary event

SEAL-PLAN §B.4 G6. Nonnegative summable deterministic weights and Gaussian
fourth moments give the square-root event probability bound. Independence
is not needed. The event restriction is unnormalized throughout.
-/

public section

namespace WaveTurbulence.MainGlue
open MeasureTheory ProbabilityTheory

/-- G6 for arbitrary nonnegative summable weights, including every Schwartz lattice envelope. -/
theorem integral_gaussian_mass_restrict_le {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} [IsProbabilityMeasure P] (g : ι → Ω → ℂ)
    (hg : ∀ i, HasLaw (g i) stdComplexGaussian P) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsa : Summable a) (A : Set Ω) :
    (∫ ω in A, ∑' i, a i * ‖g i ω‖ ^ 2 ∂P) ≤
      Real.sqrt 2 * Real.sqrt (P.real A) * ∑' i, a i := by
  let f : ι → Ω → ℝ := fun i ω => a i * ‖g i ω‖ ^ 2
  have hf0 (i : ι) (ω : Ω) : 0 ≤ f i ω := mul_nonneg (ha i) (sq_nonneg _)
  have hfi (i : ι) : Integrable (f i) P :=
    (Probability.integrable_norm_pow_of_hasLaw (hg i) 2).const_mul _
  have hfull (i : ι) : (∫ ω, ‖f i ω‖ ∂P) = a i := by
    simp_rw [Real.norm_of_nonneg (hf0 i _)]
    change (∫ ω, a i * ‖g i ω‖ ^ 2 ∂P) = _
    rw [integral_const_mul]
    have h := Probability.integral_norm_even_of_hasLaw (hg i) 1
    norm_num at h
    rw [h, mul_one]
  have hsum : Summable (fun i => ∫ ω in A, ‖f i ω‖ ∂P) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun i => (integral_mono_measure P.restrict_le_self (ae_of_all _ (fun _ => norm_nonneg _))
        (hfi i).norm).trans_eq (hfull i)) hsa
  have h := hasSum_integral_of_summable_integral_norm (fun i => (hfi i).integrableOn) hsum
  change (∫ ω in A, ∑' i, f i ω ∂P) ≤ _
  rw [← h.tsum_eq, ← tsum_mul_left]
  apply h.summable.tsum_le_tsum _ (hsa.mul_left (Real.sqrt 2 * Real.sqrt (P.real A)))
  intro i
  change (∫ ω in A, a i * ‖g i ω‖ ^ 2 ∂P) ≤ _
  rw [integral_const_mul]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (Probability.integral_norm_sq_restrict_le (hg i) A) (ha i)

end WaveTurbulence.MainGlue
