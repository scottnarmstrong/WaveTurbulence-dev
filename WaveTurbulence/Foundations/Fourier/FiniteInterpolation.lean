/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-!
# Finite-dimensional complex interpolation

The analytic coefficient families used in the Riesz–Thorin proof of
Hausdorff–Young. Zero coefficients stay zero, and every nonzero coefficient
uses an entire exponential, avoiding branch-cut assumptions on complex powers.
-/

public section

open scoped ComplexConjugate

namespace WaveTurbulence.Fourier

/-- The entire coefficient family for interpolation between `L¹` and `L²`. -/
@[expose] noncomputable def interpolationCoefficient (p : ℝ) (a z : ℂ) : ℂ :=
  if a = 0 then 0 else a / (‖a‖ : ℂ) * Complex.exp ((p : ℂ) * (1 - z / 2) * Real.log ‖a‖)

@[fun_prop] theorem interpolationCoefficient_differentiable (p : ℝ) (a : ℂ) :
    Differentiable ℂ (interpolationCoefficient p a) := by
  change Differentiable ℂ (fun z => interpolationCoefficient p a z)
  by_cases ha : a = 0
  · simp only [interpolationCoefficient, ite_eq_left ha]
    fun_prop
  · simp only [interpolationCoefficient, ite_eq_right ha]
    fun_prop

/-- The norm of the analytic coefficient depends only on the real part. -/
theorem norm_interpolationCoefficient {p : ℝ} (hp : 0 < p) (a z : ℂ)
    (hz : z.re ≤ 1) :
    ‖interpolationCoefficient p a z‖ = ‖a‖ ^ (p * (1 - z.re / 2)) := by
  have hq : 0 < p * (1 - z.re / 2) := mul_pos hp (by linarith)
  by_cases ha : a = 0
  · simp [interpolationCoefficient, ha, Real.zero_rpow hq.ne']
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  rw [interpolationCoefficient, ite_eq_right ha, norm_mul, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hna, div_self hna.ne', one_mul,
    Complex.norm_exp, Real.rpow_def_of_pos hna]
  congr 1
  simp [Complex.mul_re, Complex.div_ofNat_re]
  ring

/-- At the interpolation parameter, the original coefficient is recovered. -/
theorem interpolationCoefficient_eq {p θ : ℝ} (hθ : p * (1 - θ / 2) = 1)
    (a : ℂ) : interpolationCoefficient p a (θ : ℂ) = a := by
  by_cases ha : a = 0
  · simp [interpolationCoefficient, ha]
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have he : (p : ℂ) * (1 - (θ : ℂ) / 2) = 1 := by exact_mod_cast hθ
  rw [interpolationCoefficient, ite_eq_right ha, he, one_mul,
    ← Complex.ofReal_exp, Real.exp_log hna]
  exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hna.ne')

/-- Uniform coefficient bounds on the closed interpolation strip. -/
theorem norm_interpolationCoefficient_le {p : ℝ} (hp : 0 < p) (a z : ℂ)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖interpolationCoefficient p a z‖ ≤ 1 + ‖a‖ ^ p := by
  rw [norm_interpolationCoefficient hp a z hz1]
  have hq : 0 ≤ p * (1 - z.re / 2) := mul_nonneg hp.le (by linarith)
  rcases le_total 1 ‖a‖ with ha | ha
  · have h := Real.rpow_le_rpow_of_exponent_le ha (show p * (1 - z.re / 2) ≤ p by nlinarith)
    exact h.trans (le_add_of_nonneg_left zero_le_one)
  · have h := Real.rpow_le_one (norm_nonneg a) ha hq
    exact h.trans (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg a) p))

/-- Normalized finite-dimensional bilinear Riesz–Thorin interpolation
between the `(L¹,L¹)` and `(L²,L²)` bounds. This is the analytic core of
Hausdorff–Young; the endpoint bounds are hypotheses of this general theorem. -/
theorem finite_bilinear_interpolation {n m : ℕ}
    (B : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ) →L[ℂ] ℂ)
    (w : Fin n → ℝ) (v : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j)
    (h1 : ∀ a b, ‖B a b‖ ≤ (∑ i, w i * ‖a i‖) * (∑ j, v j * ‖b j‖))
    (h2 : ∀ a b, ‖B a b‖ ≤ Real.sqrt (∑ i, w i * ‖a i‖ ^ 2) *
      Real.sqrt (∑ j, v j * ‖b j‖ ^ 2))
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (a : Fin n → ℂ) (b : Fin m → ℂ)
    (ha : ∑ i, w i * ‖a i‖ ^ p = 1) (hb : ∑ j, v j * ‖b j‖ ^ p = 1) :
    ‖B a b‖ ≤ 1 := by
  have hp : 0 < p := zero_lt_one.trans_le hp1
  let A := fun z : ℂ => fun i => interpolationCoefficient p (a i) z
  let C := fun z : ℂ => fun j => interpolationCoefficient p (b j) z
  let F := fun z : ℂ => B (A z) (C z)
  have hAd : Differentiable ℂ A := by
    apply differentiable_pi.mpr
    intro i
    exact interpolationCoefficient_differentiable p (a i)
  have hCd : Differentiable ℂ C := by
    apply differentiable_pi.mpr
    intro j
    exact interpolationCoefficient_differentiable p (b j)
  have hFd : Differentiable ℂ F := (B.differentiable.comp hAd).clm_apply hCd
  have hsumA0 (z : ℂ) (hz : z.re = 0) : ∑ i, w i * ‖A z i‖ = 1 := by
    dsimp [A]
    simp_rw [norm_interpolationCoefficient hp _ z (by linarith), hz, zero_div, sub_zero, mul_one]
    exact ha
  have hsumC0 (z : ℂ) (hz : z.re = 0) : ∑ j, v j * ‖C z j‖ = 1 := by
    dsimp [C]
    simp_rw [norm_interpolationCoefficient hp _ z (by linarith), hz, zero_div, sub_zero, mul_one]
    exact hb
  have hpow (q : ℂ) (z : ℂ) (hz : z.re = 1) :
      ‖interpolationCoefficient p q z‖ ^ 2 = ‖q‖ ^ p := by
    rw [norm_interpolationCoefficient hp _ z hz.le, hz]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg q)]
    congr 1
    norm_num
    ring
  have hsumA1 (z : ℂ) (hz : z.re = 1) : ∑ i, w i * ‖A z i‖ ^ 2 = 1 := by
    dsimp [A]
    simp_rw [hpow _ z hz]
    exact ha
  have hsumC1 (z : ℂ) (hz : z.re = 1) : ∑ j, v j * ‖C z j‖ ^ 2 = 1 := by
    dsimp [C]
    simp_rw [hpow _ z hz]
    exact hb
  have hleft (z : ℂ) (hz : z ∈ Complex.re ⁻¹' {(0 : ℝ)}) : ‖F z‖ ≤ 1 := by
    have hh := h1 (A z) (C z)
    simpa only [hsumA0 z hz, hsumC0 z hz, one_mul] using hh
  have hright (z : ℂ) (hz : z ∈ Complex.re ⁻¹' {(1 : ℝ)}) : ‖F z‖ ≤ 1 := by
    have hh := h2 (A z) (C z)
    simpa only [hsumA1 z hz, hsumC1 z hz, Real.sqrt_one, one_mul] using hh
  have hBdd : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨((∑ i, w i) + 1) * ((∑ j, v j) + 1), ?_⟩
    rintro t ⟨z, hz, rfl⟩
    have hz0 : 0 ≤ z.re := hz.1
    have hz1 : z.re ≤ 1 := hz.2
    have hA : (∑ i, w i * ‖A z i‖) ≤ (∑ i, w i) + 1 := by
      rw [← ha, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_add, mul_one] using mul_le_mul_of_nonneg_left
        (norm_interpolationCoefficient_le hp (a i) z hz0 hz1) (hw i)
    have hC : (∑ j, v j * ‖C z j‖) ≤ (∑ j, v j) + 1 := by
      rw [← hb, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      simpa only [mul_add, mul_one] using mul_le_mul_of_nonneg_left
        (norm_interpolationCoefficient_le hp (b j) z hz0 hz1) (hv j)
    exact (h1 (A z) (C z)).trans (mul_le_mul hA hC
      (Finset.sum_nonneg (fun j _ => mul_nonneg (hv j) (norm_nonneg _)))
      (add_nonneg (Finset.sum_nonneg (fun i _ => hw i)) zero_le_one))
  let θ := 2 - 2 / p
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    have hh : 2 / p ≤ 2 := (div_le_iff₀ hp).mpr (by linarith)
    linarith
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    have hh : 1 ≤ 2 / p := (le_div_iff₀ hp).mpr (by simpa using hp2)
    linarith
  have he : p * (1 - θ / 2) = 1 := by dsimp [θ]; field_simp; ring
  have hAe : A (θ : ℂ) = a := funext (fun i => interpolationCoefficient_eq he (a i))
  have hCe : C (θ : ℂ) = b := funext (fun j => interpolationCoefficient_eq he (b j))
  have hh := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := F) (z := (θ : ℂ)) (a := 1) (b := 1)
    (by norm_num : (0 : ℝ) < 1) ⟨hθ0, hθ1⟩
    ⟨hFd.differentiableOn, hFd.continuous.continuousOn⟩ hBdd hleft hright
  simpa only [F, hAe, hCe, Real.one_rpow, one_mul] using hh

end WaveTurbulence.Fourier
