/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerExtraction
public import WaveTurbulence.Foundations.CountLemmas.PowerAbsorption
/-! Numerical absorption with moment-dependent small delta and late high norms. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.FC23
open Filter

def extractionRadius (S N : ℕ) (C U M : ℝ) : ℝ :=
  (M / (4 * (2 * N + 1 : ℕ))) ^ S / (C * (2 * N + 1 : ℕ) * U)

theorem extractionRadius_pos (S N : ℕ) {C U M : ℝ} (hC : 0 < C) (hU : 0 < U) (hM : 0 < M) :
    0 < extractionRadius S N C U M := by unfold extractionRadius; positivity

theorem extractionRadius_identity (S N : ℕ) {C U M : ℝ}
    (hC : 0 < C) (hU : 0 < U) (hM : 0 < M) :
    ((2 * N + 1 : ℕ) : ℝ) / extractionRadius S N C U M =
      4 ^ S * C * U * ((2 * N + 1 : ℕ) : ℝ) ^ (S + 2) / M ^ S := by
  unfold extractionRadius
  have hD : (((2 * N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [div_pow, mul_pow, pow_add]
  field_simp

/-- Every fixed polynomial in the original total order is absorbed by a late
power of L, uniformly over the full polylogarithmic order range. -/
theorem eventually_degree_cost {C b : ℝ} (hC : 0 ≤ C) (hb : 0 < b) (m X : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ N : ℕ, (N : ℝ) ≤ Real.log L ^ X →
      C * (((2 * N + 1 : ℕ) : ℝ)) ^ m ≤ L ^ b := by
  have hh := CountLemmas.eventually_monomial_log_le (a := 0) (b := b)
    (C := C * 3 ^ m) hb (by positivity) (X * m)
  filter_upwards [hh, Real.tendsto_log_atTop.eventually_ge_atTop 1] with L hL hlog
  intro N hN
  have hlog0 : 0 ≤ Real.log L := zero_le_one.trans hlog
  have hpow : 1 ≤ (1 + Real.log L) ^ X := one_le_pow₀ (by linarith)
  have hcmp : (N : ℝ) ≤ (1 + Real.log L) ^ X :=
    hN.trans (pow_le_pow_left₀ hlog0 (by linarith) X)
  have hD : (((2 * N + 1 : ℕ) : ℝ)) ≤ 3 * (1 + Real.log L) ^ X := by push_cast; linarith
  calc
    _ ≤ C * (3 * (1 + Real.log L) ^ X) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hD m) hC
    _ = C * 3 ^ m * L ^ (0 : ℝ) * (1 + Real.log L) ^ (X * m) := by
      rw [mul_pow, ← pow_mul, Real.rpow_zero]; ring
    _ ≤ _ := hL
end WaveTurbulence.FC23
