/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.Cumulant.Gaussian
public import WaveTurbulence.Foundations.MainGlue.GaussianLaw
/-! TARGET L708–709: Gaussian moments, integrability and higher cumulants of the initial data. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory ProbabilityTheory Finset

/-- Scaling of a signed coefficient by its deterministic real square-root envelope. -/
theorem signed_initialCoeff {d : ℕ} {Ω : Type*} (L : ℝ) (φ : Mom d → ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) (ω : Ω) (n : Fin d → ℤ) (ζ : ℤˣ) :
    zpowSign ζ (initialCoeff L φ g ω n) = (Real.sqrt (φ (latticePoint L n)) : ℂ) *
      (if decide (ζ = 1) then g n ω else star (g n ω)) := by
  classical
  by_cases hζ : ζ = 1
  · simp [zpowSign, hζ, initialCoeff]
  · simp [zpowSign, hζ, initialCoeff]

theorem initial_signed_prod_integrable {d w : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {g : (Fin d → ℤ) → Ω → ℂ} (hg : iIndepFun g μ)
    (hlaw : ∀ n, HasLaw (g n) stdComplexGaussian μ) (L : ℝ) (φ : Mom d → ℝ)
    (n : Fin w → (Fin d → ℤ)) (ζ : Fin w → ℤˣ) :
    Integrable (fun ω => ∏ j, zpowSign (ζ j) (initialCoeff L φ g ω (n j))) μ := by
  classical
  simp_rw [signed_initialCoeff, Finset.prod_mul_distrib]
  exact (integrable_signed_prod hg hlaw Finset.univ n (fun j => decide (ζ j = 1))).const_mul _

/-- Every nonempty Gaussian initial cumulant of order at least three vanishes. -/
theorem initial_higher_cumulant_zero {d w : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {g : (Fin d → ℤ) → Ω → ℂ} (hg : iIndepFun g μ)
    (hlaw : ∀ n, HasLaw (g n) stdComplexGaussian μ) (hw : 3 ≤ w) (L : ℝ)
    (φ : Mom d → ℝ) (n : Fin w → (Fin d → ℤ)) (ζ : Fin w → ℤˣ) :
    jointCumulant μ (fun j ω => zpowSign (ζ j) (initialCoeff L φ g ω (n j))) Finset.univ = 0 := by
  classical
  have : Nonempty (Fin w) := ⟨⟨0, by omega⟩⟩
  change cumulant μ _ Finset.univ = 0
  simp_rw [signed_initialCoeff]
  rw [cumulant_mul, cumulant_signed_eq_zero_of_card_ne_two hg hlaw Finset.univ
    Finset.univ_nonempty n (fun j => decide (ζ j = 1)) (by simpa using (show w ≠ 2 by omega)), mul_zero]

/-- Unit diagonal covariance and zero off-diagonal covariance, including repeated indices. -/
theorem gaussian_covariance {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    {μ : Measure Ω} {g : ι → Ω → ℂ} (hg : iIndepFun g μ)
    (hlaw : ∀ i, HasLaw (g i) stdComplexGaussian μ) (i j : ι) :
    (∫ ω, g i ω * star (g j ω) ∂μ) = if i = j then 1 else 0 := by
  have h := integral_signed_prod_eq_prod_factorial hg hlaw (Finset.univ : Finset (Fin 2))
    ![i, j] ![true, false]
  by_cases hij : i = j
  · subst j
    simpa [Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton] using h
  · simpa [Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, hij, Ne.symm hij] using h

/-- The two-point function of the frozen initial data is exactly the sampled profile. -/
theorem initial_covariance {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {g : (Fin d → ℤ) → Ω → ℂ} (hg : iIndepFun g μ)
    (hlaw : ∀ n, HasLaw (g n) stdComplexGaussian μ) (L : ℝ) (φ : Mom d → ℝ)
    (hφ : ∀ k, 0 ≤ φ k) (n n' : Fin d → ℤ) :
    (∫ ω, initialCoeff L φ g ω n * (starRingEnd ℂ) (initialCoeff L φ g ω n') ∂μ) =
      if n = n' then (φ (latticePoint L n) : ℂ) else 0 := by
  classical
  have he (ω : Ω) : initialCoeff L φ g ω n * (starRingEnd ℂ) (initialCoeff L φ g ω n') =
      ((Real.sqrt (φ (latticePoint L n)) : ℂ) * (Real.sqrt (φ (latticePoint L n')) : ℂ)) *
        (g n ω * star (g n' ω)) := by
    simp [initialCoeff, mul_assoc, mul_left_comm, mul_comm]
  simp_rw [he]
  rw [integral_const_mul, gaussian_covariance hg hlaw]
  split_ifs with h
  · subst n'
    rw [mul_one, ← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (hφ _)]
  · rw [mul_zero]

end WaveTurbulence.Induct
