/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.FrequencyIntegration

/-!
# Finite nonstationary frequency tails

Summing the exact identities retains the cancellation in the endpoint
reciprocals. Only the remainder is estimated term by term.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- The exact finite tail identity on integer endpoints. -/
theorem sum_integral_expPhase_sub_frequency {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (a b : ℤ) (S : Finset ℤ)
    (hne : ∀ ν ∈ S, ∀ x ∈ uIcc (a : ℝ) b, deriv f x - ν ≠ 0) :
    (∑ ν ∈ S, ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)) =
      (expPhase (f b) * ((∑ ν ∈ S, (deriv f b - ν)⁻¹ : ℝ) : ℂ) -
       expPhase (f a) * ((∑ ν ∈ S, (deriv f a - ν)⁻¹ : ℝ) : ℂ) +
       ∑ ν ∈ S, ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x) *
         ((deriv (deriv f) x / (deriv f x - ν) ^ 2 : ℝ) : ℂ)) /
           ((2 * Real.pi : ℂ) * Complex.I) := by
  trans ∑ ν ∈ S,
    (expPhase (f b) * (((deriv f b - ν)⁻¹ : ℝ) : ℂ) -
     expPhase (f a) * (((deriv f a - ν)⁻¹ : ℝ) : ℂ) +
     ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x) *
       ((deriv (deriv f) x / (deriv f x - ν) ^ 2 : ℝ) : ℂ)) /
         ((2 * Real.pi : ℂ) * Complex.I)
  · exact Finset.sum_congr rfl (fun ν hν => integral_expPhase_sub_frequency hf a b ν (hne ν hν))
  · rw [← Finset.sum_div]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Complex.ofReal_sum,
    Finset.mul_sum]

/-- Quantitative finite tail bound. Endpoint cancellation is preserved;
the actual second derivative controls the integrated square kernel. -/
theorem norm_sum_integral_expPhase_sub_frequency_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (a b : ℤ) (hab : a ≤ b) (S : Finset ℤ)
    (hne : ∀ ν ∈ S, ∀ x ∈ uIcc (a : ℝ) b, deriv f x - ν ≠ 0) :
    ‖∑ ν ∈ S, ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x)‖ ≤
      (|∑ ν ∈ S, (deriv f b - ν)⁻¹| + |∑ ν ∈ S, (deriv f a - ν)⁻¹| +
        ∫ x in (a : ℝ)..b, |deriv (deriv f) x| *
          ∑ ν ∈ S, ((deriv f x - ν) ^ 2)⁻¹) / (2 * Real.pi) := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hi (ν : ℤ) (hν : ν ∈ S) :
      IntervalIntegrable (fun x => |deriv (deriv f) x| * ((deriv f x - ν) ^ 2)⁻¹)
        volume (a : ℝ) b := by
    apply ContinuousOn.intervalIntegrable (μ := volume)
    exact hf1.continuous_deriv_one.abs.continuousOn.mul
      (((hf1.continuous.continuousOn.sub continuousOn_const).pow 2).inv₀
        (fun x hx => pow_ne_zero 2 (hne ν hν x hx)))
  have hR (ν : ℤ) (hν : ν ∈ S) :
      ‖∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x) *
          ((deriv (deriv f) x / (deriv f x - ν) ^ 2 : ℝ) : ℂ)‖ ≤
        ∫ x in (a : ℝ)..b, |deriv (deriv f) x| * ((deriv f x - ν) ^ 2)⁻¹ := by
    have hh := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun x => expPhase (f x - (ν : ℝ) * x) *
        ((deriv (deriv f) x / (deriv f x - ν) ^ 2 : ℝ) : ℂ)) habR
    simpa only [norm_mul, norm_expPhase, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_inv, abs_pow, sq_abs, div_eq_mul_inv] using hh
  have hsum : ‖∑ ν ∈ S, ∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x) *
          ((deriv (deriv f) x / (deriv f x - ν) ^ 2 : ℝ) : ℂ)‖ ≤
      ∫ x in (a : ℝ)..b, |deriv (deriv f) x| * ∑ ν ∈ S, ((deriv f x - ν) ^ 2)⁻¹ := by
    calc
      _ ≤ ∑ ν ∈ S, ‖∫ x in (a : ℝ)..b, expPhase (f x - (ν : ℝ) * x) *
          ((deriv (deriv f) x / (deriv f x - ν) ^ 2 : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ ν ∈ S, ∫ x in (a : ℝ)..b, |deriv (deriv f) x| * ((deriv f x - ν) ^ 2)⁻¹ :=
        Finset.sum_le_sum (fun ν hν => hR ν hν)
      _ = _ := by
        rw [← intervalIntegral.integral_finsetSum hi]
        simp only [Finset.mul_sum]
  rw [sum_integral_expPhase_sub_frequency hf a b S hne, norm_div]
  have hden : ‖(2 * Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hden]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ‖expPhase (f b) * ((∑ ν ∈ S, (deriv f b - ν)⁻¹ : ℝ) : ℂ) -
          expPhase (f a) * ((∑ ν ∈ S, (deriv f a - ν)⁻¹ : ℝ) : ℂ)‖ +
        (∫ x in (a : ℝ)..b, |deriv (deriv f) x| * ∑ ν ∈ S, ((deriv f x - ν) ^ 2)⁻¹) :=
      (norm_add_le _ _).trans (add_le_add le_rfl hsum)
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      have hh := norm_sub_le
        (expPhase (f b) * ((∑ ν ∈ S, (deriv f b - ν)⁻¹ : ℝ) : ℂ))
        (expPhase (f a) * ((∑ ν ∈ S, (deriv f a - ν)⁻¹ : ℝ) : ℂ))
      simpa only [norm_mul, norm_expPhase, one_mul, Complex.norm_real, Real.norm_eq_abs] using hh

end WaveTurbulence.VdCB
