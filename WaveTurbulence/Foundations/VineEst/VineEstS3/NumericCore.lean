/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The real-number core of the Step 3 constant bookkeeping

All the powers of `L`, `δ` are reduced to the atoms `s = √δ`, `u = L^{d-γ}`, `Le = L^{e₁}` and the claim is the
polynomial inequality of TARGET's `(C₁√δ)^{n₍₂₎}` form with `C* = K₁ X √2`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3

/-- The constants of the bookkeeping. -/
noncomputable def numK1 (cc c0 c : ℝ) : ℝ := cc * 3 * c0 * c
noncomputable def numX (c1 cf cb c : ℝ) : ℝ := 6 * c1 ^ 2 * cf ^ 2 * cb ^ 2 * c ^ 5
noncomputable def numCstar (cc c0 c1 cf cb c : ℝ) : ℝ := numK1 cc c0 c * numX c1 cf cb c * Real.sqrt 2

theorem numCstar_nonneg {cc c0 c1 cf cb c : ℝ} (hcc : 0 ≤ cc) (hc0 : 0 ≤ c0) (hc : 0 ≤ c) :
    0 ≤ numCstar cc c0 c1 cf cb c := by
  unfold numCstar numK1 numX; positivity

theorem one_le_numCstar {cc c0 c1 cf cb c : ℝ} (hc : 1 ≤ c) (hcc : 1 ≤ cc) (hc0 : 1 ≤ c0) (hc1 : 1 ≤ c1)
    (hcf : 1 ≤ cf) (hcb : 1 ≤ cb) : 1 ≤ numCstar cc c0 c1 cf cb c := by
  have hcc0 : 1 ≤ cc * c0 := one_le_mul_of_one_le_of_one_le hcc hc0
  have hK1 : 1 ≤ numK1 cc c0 c := by
    unfold numK1
    have : cc * 3 * c0 * c = 3 * (cc * c0) * c := by ring
    rw [this]; nlinarith
  have hX : 1 ≤ numX c1 cf cb c := by
    unfold numX
    have h1 : 1 ≤ c1 ^ 2 := one_le_pow₀ hc1
    have h2 : 1 ≤ cf ^ 2 := one_le_pow₀ hcf
    have h3 : 1 ≤ cb ^ 2 := one_le_pow₀ hcb
    have h4 : 1 ≤ c ^ 5 := one_le_pow₀ hc
    nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity), mul_le_mul (mul_le_mul h1 h2 zero_le_one (by positivity)) h3 zero_le_one (by positivity)]
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  unfold numCstar
  nlinarith [mul_le_mul hK1 hX zero_le_one (by linarith)]

theorem numeric_core (M Sn : ℕ) (hM : 1 ≤ M) {c s u Le cc c0 c1 cf cb : ℝ} (hc : 1 ≤ c) (hs : 0 < s) (hu : 0 < u)
    (hLe : 0 ≤ Le) (hcc : 1 ≤ cc) (hc0 : 1 ≤ c0) (hc1 : 1 ≤ c1) (hcf : 1 ≤ cf) (hcb : 1 ≤ cb) :
    (s ^ 2 / (2 * u)) ^ M * (cc * (3 ^ (M + 1) * (c0 * c1 ^ (2 * M) * (c * (c * s⁻¹) ^ M * (u ^ M * Le))) *
      cf ^ (2 * M) * ((2 * cb * c ^ 2) ^ (2 * M) * (2 * c ^ 2 * s ^ 2) ^ Sn))) ≤
      (numCstar cc c0 c1 cf cb c * s) ^ (M + 2 * Sn) * Le := by
  have hcc0 : 1 ≤ cc * c0 := one_le_mul_of_one_le_of_one_le hcc hc0
  have hK1 : 1 ≤ numK1 cc c0 c := by
    unfold numK1
    have : cc * 3 * c0 * c = 3 * (cc * c0) * c := by ring
    rw [this]; nlinarith
  have hX : 1 ≤ numX c1 cf cb c := by
    unfold numX
    have h1 : 1 ≤ c1 ^ 2 := one_le_pow₀ hc1
    have h2 : 1 ≤ cf ^ 2 := one_le_pow₀ hcf
    have h3 : 1 ≤ cb ^ 2 := one_le_pow₀ hcb
    have h4 : 1 ≤ c ^ 5 := one_le_pow₀ hc
    nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity), mul_le_mul (mul_le_mul h1 h2 zero_le_one (by positivity)) h3 zero_le_one (by positivity)]
  set K1 := numK1 cc c0 c with hK1d
  set X := numX c1 cf cb c with hXd
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hC : K1 * X ≤ numCstar cc c0 c1 cf cb c := by
    unfold numCstar; nlinarith [mul_pos (lt_of_lt_of_le one_pos hK1) (lt_of_lt_of_le one_pos hX)]
  have hCc : Real.sqrt 2 * c ≤ numCstar cc c0 c1 cf cb c := by
    have h1 : c ≤ K1 := by
      rw [hK1d]; unfold numK1
      have : cc * 3 * c0 * c = 3 * (cc * c0) * c := by ring
      rw [this]; nlinarith
    have h2 : K1 ≤ K1 * X := by nlinarith
    have : c ≤ K1 * X := h1.trans h2
    unfold numCstar
    calc Real.sqrt 2 * c ≤ Real.sqrt 2 * (K1 * X) := by gcongr
      _ = K1 * X * Real.sqrt 2 := by ring
  set C := numCstar cc c0 c1 cf cb c with hCd
  have hC0 : 0 ≤ C := by linarith [mul_pos (lt_of_lt_of_le one_pos hK1) (lt_of_lt_of_le one_pos hX)]
  -- the exact value of the left side
  have hlhs : (s ^ 2 / (2 * u)) ^ M * (cc * (3 ^ (M + 1) * (c0 * c1 ^ (2 * M) * (c * (c * s⁻¹) ^ M * (u ^ M * Le))) *
      cf ^ (2 * M) * ((2 * cb * c ^ 2) ^ (2 * M) * (2 * c ^ 2 * s ^ 2) ^ Sn))) =
      K1 * X ^ M * s ^ M * (2 * c ^ 2 * s ^ 2) ^ Sn * Le := by
    have hB : (s ^ 2 / (2 * u)) * 3 * c1 ^ 2 * (c * s⁻¹) * u * cf ^ 2 * (2 * cb * c ^ 2) ^ 2 = X * s := by
      rw [hXd]; unfold numX
      field_simp
      ring
    have hA : ∀ m : ℕ, (s ^ 2 / (2 * u)) ^ m * (cc * (3 ^ (m + 1) * (c0 * c1 ^ (2 * m) * (c * (c * s⁻¹) ^ m * (u ^ m * Le))) *
        cf ^ (2 * m) * ((2 * cb * c ^ 2) ^ (2 * m) * (2 * c ^ 2 * s ^ 2) ^ Sn))) =
        (cc * 3 * c0 * c * Le * (2 * c ^ 2 * s ^ 2) ^ Sn) *
          ((s ^ 2 / (2 * u)) * 3 * c1 ^ 2 * (c * s⁻¹) * u * cf ^ 2 * (2 * cb * c ^ 2) ^ 2) ^ m := by
      intro m
      induction m with
      | zero => simp; ring
      | succ m ih =>
        have e : (s ^ 2 / (2 * u)) ^ (m + 1) * (cc * (3 ^ (m + 1 + 1) * (c0 * c1 ^ (2 * (m + 1)) *
            (c * (c * s⁻¹) ^ (m + 1) * (u ^ (m + 1) * Le))) * cf ^ (2 * (m + 1)) *
            ((2 * cb * c ^ 2) ^ (2 * (m + 1)) * (2 * c ^ 2 * s ^ 2) ^ Sn))) =
            ((s ^ 2 / (2 * u)) ^ m * (cc * (3 ^ (m + 1) * (c0 * c1 ^ (2 * m) * (c * (c * s⁻¹) ^ m * (u ^ m * Le))) *
              cf ^ (2 * m) * ((2 * cb * c ^ 2) ^ (2 * m) * (2 * c ^ 2 * s ^ 2) ^ Sn)))) *
            ((s ^ 2 / (2 * u)) * 3 * c1 ^ 2 * (c * s⁻¹) * u * cf ^ 2 * (2 * cb * c ^ 2) ^ 2) := by ring
        rw [e, ih]; ring
    rw [hA M, hB, mul_pow, hK1d]; unfold numK1
    ring
  rw [hlhs]
  have hKM : K1 * X ^ M ≤ (K1 * X) ^ M := by
    rw [mul_pow]
    have : K1 ≤ K1 ^ M := by
      calc K1 = K1 ^ 1 := (pow_one _).symm
        _ ≤ K1 ^ M := pow_le_pow_right₀ hK1 hM
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h2c : (2 * c ^ 2 * s ^ 2) ^ Sn ≤ (C * s) ^ (2 * Sn) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    have : 2 * c ^ 2 * s ^ 2 = (Real.sqrt 2 * c * s) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    rw [this]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_right hCc hs.le
  calc K1 * X ^ M * s ^ M * (2 * c ^ 2 * s ^ 2) ^ Sn * Le
      ≤ (C * s) ^ M * (C * s) ^ (2 * Sn) * Le := by
        gcongr
        · calc K1 * X ^ M * s ^ M ≤ (K1 * X) ^ M * s ^ M := by gcongr
            _ ≤ C ^ M * s ^ M := by gcongr
            _ = (C * s) ^ M := (mul_pow _ _ _).symm
    _ = (C * s) ^ (M + 2 * Sn) * Le := by rw [pow_add]

end WaveTurbulence.VineEstS3
