/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Gaussian.ComplexGaussian
public import WaveTurbulence.Foundations.Probability.RestrictedCauchySchwarz

/-!
# Gaussian absolute moments and event estimates

TARGET L819 uses Cauchy–Schwarz on the initial Gaussian coefficients.
For the frozen normalization, the fourth absolute moment is two, giving
`√2 P(A)^(1/2)` for the restricted second moment.
-/

public section

namespace WaveTurbulence.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → ℂ}

/-- All even absolute moments of a normalized complex Gaussian are factorials. -/
theorem integral_norm_even_of_hasLaw (hg : HasLaw g stdComplexGaussian P) (p : ℕ) :
    (∫ ω, ‖g ω‖ ^ (2 * p) ∂P) = p.factorial := by
  have hp (ω : Ω) : ((‖g ω‖ ^ (2 * p) : ℝ) : ℂ) = g ω ^ p * star (g ω) ^ p := by
    rw [pow_mul, Complex.ofReal_pow, Complex.ofReal_pow, ← Complex.mul_conj', mul_pow]
    rfl
  have h := integral_monomial_of_hasLaw_stdComplexGaussian hg p p
  simp only [eq_self, ite_true] at h
  simp_rw [← hp] at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_natCast] using h)

/-- Every finite absolute moment is integrable under the specified Gaussian law. -/
theorem integrable_norm_pow_of_hasLaw (hg : HasLaw g stdComplexGaussian P) (p : ℕ) :
    Integrable (fun ω => ‖g ω‖ ^ p) P := by
  have hid : MemLp (fun z : ℂ => z) (p : ℝ≥0∞) stdComplexGaussian := by
    simpa only [ENNReal.coe_natCast] using memLp_id_stdComplexGaussian (p : ℝ≥0)
  have hm : MemLp g (p : ℝ≥0∞) P := by
    simpa only [Function.comp_def] using hg.memLp_comp hid
  let : IsProbabilityMeasure P := hg.isProbabilityMeasure
  exact hm.integrable_norm_pow'

/-- The precise Gaussian event bound used for the initial datum (TARGET L819). -/
theorem integral_norm_sq_restrict_le [IsProbabilityMeasure P]
    (hg : HasLaw g stdComplexGaussian P) (A : Set Ω) :
    (∫ ω in A, ‖g ω‖ ^ 2 ∂P) ≤ Real.sqrt 2 * Real.sqrt (P.real A) := by
  have hi := integrable_norm_pow_of_hasLaw hg 4
  have hf : MemLp (fun ω => ‖g ω‖ ^ 2) 2 P :=
    (memLp_two_iff_integrable_sq (hg.aemeasurable.aestronglyMeasurable.norm.pow 2)).mpr
      (by simpa only [Pi.pow_apply, ← pow_mul] using hi)
  have h := norm_setIntegral_le_sqrt_measure_mul hf A
  have heq : (fun ω => ‖‖g ω‖ ^ 2‖ ^ 2) = (fun ω => ‖g ω‖ ^ (2 * 2)) := by
    funext ω
    rw [Real.norm_of_nonneg (sq_nonneg _), ← pow_mul]
  rw [heq, integral_norm_even_of_hasLaw hg 2] at h
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_ofNat] at h
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, mul_comm] using h)

/-- The first absolute moment is at most one. -/
theorem integral_norm_le_one [IsProbabilityMeasure P]
    (hg : HasLaw g stdComplexGaussian P) : (∫ ω, ‖g ω‖ ∂P) ≤ 1 := by
  have hid : MemLp (fun z : ℂ => z) 2 stdComplexGaussian := by
    simpa using memLp_id_stdComplexGaussian 2
  have hf : MemLp g 2 P := by simpa only [Function.comp_def] using hg.memLp_comp hid
  have h := norm_setIntegral_le_sqrt_measure_mul hf.norm Set.univ
  have heq : (fun ω => ‖‖g ω‖‖ ^ 2) = (fun ω => ‖g ω‖ ^ (2 * 1)) := by
    funext ω
    simp only [Real.norm_of_nonneg (norm_nonneg _)]
  rw [heq, integral_norm_even_of_hasLaw hg 1] at h
  have h' : |∫ ω, ‖g ω‖ ∂P| ≤ 1 := by
    simpa only [setIntegral_univ, Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one,
      Real.sqrt_one, Nat.factorial_one, Nat.cast_one, mul_one] using h
  exact (le_abs_self _).trans h'

end WaveTurbulence.Probability
