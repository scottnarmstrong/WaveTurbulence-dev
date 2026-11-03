/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.HuaEnergy

/-!
# Monotonicity of even Fourier moments with positive coefficients

Integer-frequency orthogonality expresses an even moment as a sum of
nonnegative resonant products. Increasing nonnegative coefficients therefore
increases every even moment. This allows a positive smooth cutoff to majorize
the resonance counts in DH21 Lemma A.5.
-/

public section

open Finset
open scoped BigOperators ComplexConjugate

namespace WaveTurbulence.WeylSums

/-- Exact second-moment identity for real coefficients. -/
theorem integral_integerExponentialSum_norm_sq_real {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (freq : ι → ℤ) :
    (∫ t : ℝ in 0..1, ‖integerExponentialSum (fun i => (w i : ℂ)) freq t‖ ^ 2) =
      ∑ i : ι, ∑ j : ι, if freq i = freq j then w i * w j else 0 := by
  classical
  have hh := congrArg Complex.re (integral_integerExponentialSum_norm_sq (fun i => (w i : ℂ)) freq)
  simpa only [Complex.ofReal_re, Complex.re_sum, apply_ite Complex.re, Complex.zero_re,
    Complex.conj_ofReal, ← Complex.ofReal_mul] using hh

theorem tupleCoeff_ofReal {ι : Type*} {m : ℕ} (w : ι → ℝ) (v : Fin m → ι) :
    tupleCoeff (fun i => (w i : ℂ)) v = ((∏ i, w (v i) : ℝ) : ℂ) := by
  unfold tupleCoeff
  simpa only [Complex.ofRealHom_eq_coe] using
    (map_prod Complex.ofRealHom (fun i => w (v i)) univ).symm

/-- Exact even moment as a sum of resonant products of real coefficients. -/
theorem integral_integerExponentialSum_norm_pow_real {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (freq : ι → ℤ) (m : ℕ) :
    (∫ t : ℝ in 0..1, ‖integerExponentialSum (fun i => (w i : ℂ)) freq t‖ ^ (2 * m)) =
      ∑ u : Fin m → ι, ∑ v : Fin m → ι,
        if tupleFrequency freq u = tupleFrequency freq v then
          (∏ i, w (u i)) * (∏ i, w (v i)) else 0 := by
  have hpoint (t : ℝ) : ‖integerExponentialSum (fun i => (w i : ℂ)) freq t‖ ^ (2 * m) =
      ‖integerExponentialSum (fun v : Fin m → ι => ((∏ i, w (v i) : ℝ) : ℂ))
        (tupleFrequency freq) t‖ ^ 2 := by
    rw [show 2 * m = m * 2 by omega, pow_mul, ← norm_pow, integerExponentialSum_pow]
    rw [show tupleCoeff (m := m) (fun i => (w i : ℂ)) =
      (fun v : Fin m → ι => ((∏ i, w (v i) : ℝ) : ℂ)) from funext (tupleCoeff_ofReal w)]
  simp_rw [hpoint]
  exact integral_integerExponentialSum_norm_sq_real _ _

/-- Even moments increase under pointwise enlargement of nonnegative real coefficients. -/
theorem integral_integerExponentialSum_norm_pow_mono {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (freq : ι → ℤ) (m : ℕ)
    (hu : ∀ i, 0 ≤ u i) (huv : ∀ i, u i ≤ v i) :
    (∫ t : ℝ in 0..1, ‖integerExponentialSum (fun i => (u i : ℂ)) freq t‖ ^ (2 * m)) ≤
      ∫ t : ℝ in 0..1, ‖integerExponentialSum (fun i => (v i : ℂ)) freq t‖ ^ (2 * m) := by
  classical
  rw [integral_integerExponentialSum_norm_pow_real, integral_integerExponentialSum_norm_pow_real]
  apply sum_le_sum
  intro x _
  apply sum_le_sum
  intro y _
  split_ifs
  · exact mul_le_mul
      (prod_le_prod₀ (fun i _ => hu _) (fun i _ => huv _))
      (prod_le_prod₀ (fun i _ => hu _) (fun i _ => huv _))
      (prod_nonneg (fun i _ => hu _))
      (prod_nonneg (fun i _ => (hu _).trans (huv _)))
  · exact le_rfl

/-- At zero linear frequency all surviving resonance coefficients equal one. -/
theorem integral_gaussSum_norm_pow_zero_eq_energy (h : ℤ) (n m : ℕ) :
    (∫ s : ℝ in 0..1, ‖gaussSum s 0 h n‖ ^ (2 * m)) = quadraticEnergy h n m := by
  classical
  simp_rw [gaussSum_eq_integerExponentialSum, zero_mul, e_zero]
  have hh := integral_integerExponentialSum_norm_pow_real (fun _ : Fin (n + 1) => (1 : ℝ))
    (fun p : Fin (n + 1) => (h + (p : ℕ) : ℤ) ^ 2) m
  simp only [Complex.ofReal_one, prod_const_one, one_mul] at hh
  rw [hh]
  rw [← Fintype.sum_prod_type (fun p : (Fin m → Fin (n + 1)) × (Fin m → Fin (n + 1)) =>
    if tupleFrequency (fun k : Fin (n + 1) => (h + (k : ℕ) : ℤ) ^ 2) p.1 =
      tupleFrequency (fun k : Fin (n + 1) => (h + (k : ℕ) : ℤ) ^ 2) p.2 then (1 : ℝ) else 0)]
  simp only [quadraticEnergy, resonanceCard, tupleFrequency, ← sum_filter, sum_const,
    nsmul_eq_mul, mul_one]

end WaveTurbulence.WeylSums
