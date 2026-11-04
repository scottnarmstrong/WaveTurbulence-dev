/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ClassJR.Bump

/-! # Geometric Fourier profiles of the tree time monomials

DH23 Proposition 6.1 (time-factor bound): the literal tree time polynomial can be
extended by fixed smooth cutoffs. The landed compact-bump derivative estimate supplies
geometric bounds in every monomial degree, with fixed cubic Fourier decay.
-/

public section
noncomputable section
open scoped FourierTransform ContDiff
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR

/-- Multiplying the source time bump by a monomial differentiates its actual Fourier profile. -/
theorem iteratedDeriv_ftpi_eq_monomial {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (n : ℕ) :
    iteratedDeriv n (ftπ f) = (-((Real.pi : ℂ) * Complex.I)) ^ n •
      ftπ (fun x : ℝ => (x : ℂ) ^ n * f x) := by
  rw [iteratedDeriv_ftπ hf hc]
  unfold ftπ
  calc
    _ = 𝓕 (((-((Real.pi : ℂ) * Complex.I)) ^ n) •
        (fun w : ℝ => ((2 * w : ℝ) : ℂ) ^ n * f (2 * w))) := by
      congr 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      have he : -2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) =
          (-((Real.pi : ℂ) * Complex.I)) * ((2 * x : ℝ) : ℂ) := by push_cast; ring
      rw [he, mul_pow]
      ring
    _ = _ := VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ ℝ)
      (fun w : ℝ => ((2 * w : ℝ) : ℂ) ^ n * f (2 * w)) ((-((Real.pi : ℂ) * Complex.I)) ^ n)

/-- The cutoff monomial Fourier profiles have a geometric bound in the degree.
No order exponent and no time integration degree enters K or B. -/
theorem exists_norm_ftpi_monomial_le {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧ ∀ (n : ℕ) (ξ : ℝ),
      ‖ftπ (fun x : ℝ => (x : ℂ) ^ n * f x) ξ‖ ≤ K * B ^ n / (1 + |ξ|) ^ 3 := by
  obtain ⟨K, B, hK, hB, hb⟩ := exists_norm_iteratedDeriv_ftπ_le hf hc
  refine ⟨K, B / Real.pi, hK, div_nonneg hB Real.pi_pos.le, ?_⟩
  intro n ξ
  have hh := hb n ξ
  rw [iteratedDeriv_ftpi_eq_monomial hf hc n] at hh
  have hnorm : ‖(-((Real.pi : ℂ) * Complex.I)) ^ n‖ = Real.pi ^ n := by
    rw [norm_pow, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
  simp only [Pi.smul_apply, norm_smul, hnorm] at hh
  calc
    _ ≤ (K * B ^ n / (1 + |ξ|) ^ 3) / Real.pi ^ n :=
      (le_div_iff₀ (pow_pos Real.pi_pos n)).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by rw [div_pow]; ring

end WaveTurbulence.RegAsymp
