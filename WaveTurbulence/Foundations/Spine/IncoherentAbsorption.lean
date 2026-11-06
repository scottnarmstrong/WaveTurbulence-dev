/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentAssembly
public import WaveTurbulence.Foundations.CountLemmas.PowerAbsorption
/-! Small-delta and large-L absorption in the assembled incoherent contribution. -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter

theorem prefactor_pow_le {A b c : ℝ} (hA : 1 ≤ A) (hb : 0 ≤ b) (hab : A * b ≤ c)
    {n : ℕ} (hn : 1 ≤ n) : A * b ^ n ≤ c ^ n := by
  calc
    A * b ^ n ≤ A ^ n * b ^ n := mul_le_mul_of_nonneg_right
      (le_self_pow₀ hA (by omega)) (pow_nonneg hb _)
    _ = (A * b) ^ n := (mul_pow _ _ _).symm
    _ ≤ c ^ n := pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans hA) hb) hab _

/-- The original prefactor is absorbed once, using n≥1; no n-dependent threshold is chosen. -/
theorem incoherent_delta_absorption {C₁ δ : ℝ} (hC₁ : 1 ≤ C₁) (hδ : 0 ≤ δ)
    (hsmall : (2 * C₁) * ((12 ^ 9 : ℝ) * 4 * C₁ * δ) ≤ Real.sqrt δ)
    {n : ℕ} (hn : 1 ≤ n) :
    2 * C₁ * ((12 ^ 9 : ℝ) * 4 * C₁ * δ) ^ n ≤ δ ^ ((n : ℝ) / 2) := by
  have h := prefactor_pow_le (by linarith : 1 ≤ 2 * C₁)
    (by positivity : 0 ≤ (12 ^ 9 : ℝ) * 4 * C₁ * δ) hsmall hn
  apply h.trans_eq
  rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hδ]
  congr 1
  ring

/-- The layering prefactor is harmless uniformly over p≤D; the exponent gain pays for it. -/
theorem eventually_uniform_layering_decay (D : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ p ≤ D,
      (2 : ℝ) ^ (9 * p) * L ^ (-a) ≤ L ^ (-a / 2) := by
  have h := CountLemmas.eventually_monomial_log_le (a := -a) (b := -a / 2)
    (C := (2 : ℝ) ^ (9 * D)) (by linarith) (by positivity) 0
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro p hp
  apply (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.mul_le_mul_left 9 hp))
    (Real.rpow_nonneg hL0 _)).trans
  simpa only [pow_zero, mul_one] using hL

/-- An explicit positive threshold gives the small-delta condition, independent of order n. -/
theorem scaled_delta_le_sqrt {A δ : ℝ} (hA : 0 < A) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ (A⁻¹) ^ 2) : A * δ ≤ Real.sqrt δ := by
  have hs : Real.sqrt δ ≤ A⁻¹ := (Real.sqrt_le_iff).mpr ⟨inv_nonneg.mpr hA.le, hsmall⟩
  have hmul : A * Real.sqrt δ ≤ 1 := by
    simpa only [mul_inv_cancel₀ hA.ne'] using mul_le_mul_of_nonneg_left hs hA.le
  calc
    A * δ = (A * Real.sqrt δ) * Real.sqrt δ := by rw [mul_assoc, Real.mul_self_sqrt hδ]
    _ ≤ 1 * Real.sqrt δ := mul_le_mul_of_nonneg_right hmul (Real.sqrt_nonneg _)
    _ = _ := one_mul _

/-- The already assembled actual sum after the two numerical absorptions.
The remaining high spatial weights and derivatives are a separate source transfer step. -/
theorem norm_incoherentCoupleSum_le_absorbed (P : WTParams) (hdecay : IncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η) (hC₁ : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    {p n : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    (hn : n ≤ P.N (p + 1) ^ 4) (hnpos : 1 ≤ n) (t : ℝ)
    (ht : t ∈ Set.Icc (p : ℝ) (p + 1)) (k : Mom P.d)
    (hr : (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 / 2)
    (hsmall : (2 * P.C₁) * ((12 ^ 9 : ℝ) * 4 * P.C₁ * P.δ) ≤ Real.sqrt P.δ)
    (hlarge : (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤
      P.L ^ (-(P.gamma1 - Real.sqrt P.η) / 2)) :
    ‖incoherentCoupleSum P (inputsF P R) (p + 1) (2 * n) t k‖ ≤
      P.δ ^ ((n : ℝ) / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) / 2) := by
  apply (incoherentCoupleSum_geometric P hdecay hd hL hη (zero_le_one.trans hC₁) hδ
    hp R hR hn t ht k hr).trans
  calc
    _ = (2 * P.C₁ * ((12 ^ 9 : ℝ) * 4 * P.C₁ * P.δ) ^ n) *
        ((2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η))) := by ring
    _ ≤ _ := mul_le_mul (incoherent_delta_absorption hC₁ hδ hsmall hnpos) hlarge
      (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg hδ _)

end WaveTurbulence.LGSpine
