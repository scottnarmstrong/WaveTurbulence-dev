/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineDouble5
/-! The label count of a VC formed by two double bonds, part 6: **the count `𝔉 ≲ L^d (ρL)^d (L^{d-1} + δ⁻¹ min(R⁻¹ L^{d-2γ}, L^d))`**
(DH23 L1801 last sentence), from the shape `a = x = b`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem double_real (d : ℕ) {L γ δ R ρ : ℝ} (hd : 1 ≤ d) (hL : 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 < R)
    (hρ : 0 ≤ ρ) (hρL : 1 ≤ ρ * L) :
    ((⌊2 * 1 * L⌋₊ + 1) ^ d : ℕ) * ((⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) *
        min ((2 * (L * 2) + 1) ^ (d - 1) * (2 * (d : ℝ) * (δ⁻¹ * L ^ (-2 * γ) / 2) * L / (R / 2) + 1))
          (((⌊2 * 2 * L⌋₊ + 1) ^ d : ℕ) : ℝ) ≤
      vineG d L γ δ R ρ (9 ^ d * 5 ^ d * (2 * d)) 0 := by
  have hL0 : 0 < L := by linarith
  have hX0 : ((⌊2 * 1 * L⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * L := by
    push_cast
    have := Nat.floor_le (show 0 ≤ 2 * 1 * L by positivity)
    linarith
  have hX1 : ((⌊2 * ρ * L⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * (ρ * L) := by
    push_cast
    have := Nat.floor_le (show 0 ≤ 2 * ρ * L by positivity)
    nlinarith
  have hX2 : ((⌊2 * 2 * L⌋₊ + 1 : ℕ) : ℝ) ≤ 5 * L := by
    push_cast
    have := Nat.floor_le (show 0 ≤ 2 * 2 * L by positivity)
    linarith
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set m := min (R⁻¹ * L ^ ((d : ℝ) - 2 * γ)) (L ^ d) with hm
  have hm0 : 0 ≤ m := le_min (by positivity) (by positivity)
  -- the third factor
  have e1 : L ^ (d - 1) * L ^ (1 - 2 * γ) = L ^ ((d : ℝ) - 2 * γ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
    congr 1; push_cast [Nat.cast_sub hd]; ring
  have hB : min ((2 * (L * 2) + 1) ^ (d - 1) * (2 * (d : ℝ) * (δ⁻¹ * L ^ (-2 * γ) / 2) * L / (R / 2) + 1))
        (((⌊2 * 2 * L⌋₊ + 1) ^ d : ℕ) : ℝ) ≤ 5 ^ d * (2 * d) * (L ^ (d - 1) + δ⁻¹ * m) := by
    have hP1 : (2 * (L * 2) + 1) ^ (d - 1) * (2 * (d : ℝ) * (δ⁻¹ * L ^ (-2 * γ) / 2) * L / (R / 2) + 1) ≤
        5 ^ d * (2 * d) * (L ^ (d - 1) + δ⁻¹ * (R⁻¹ * L ^ ((d : ℝ) - 2 * γ))) := by
      have h5 : (2 * (L * 2) + 1) ^ (d - 1) ≤ (5 * L) ^ (d - 1) := by
        gcongr; linarith
      have h6 : 2 * (d : ℝ) * (δ⁻¹ * L ^ (-2 * γ) / 2) * L / (R / 2) + 1 =
          2 * d * δ⁻¹ * R⁻¹ * (L * L ^ (-2 * γ)) + 1 := by
        field_simp
      have h7 : L * L ^ (-2 * γ) = L ^ (1 - 2 * γ) := by
        rw [show (1 - 2 * γ) = 1 + (-2 * γ) by ring, Real.rpow_add hL0, Real.rpow_one]
      rw [h6, h7]
      have hLp : 0 ≤ L ^ (d - 1) := by positivity
      have h5L : (5 * L) ^ (d - 1) = 5 ^ (d - 1) * L ^ (d - 1) := mul_pow _ _ _
      have hpow : (5 : ℝ) ^ (d - 1) ≤ 5 ^ d := pow_le_pow_right₀ (by norm_num) (Nat.sub_le d 1)
      calc (2 * (L * 2) + 1) ^ (d - 1) * (2 * d * δ⁻¹ * R⁻¹ * L ^ (1 - 2 * γ) + 1)
          ≤ (5 * L) ^ (d - 1) * (2 * d * δ⁻¹ * R⁻¹ * L ^ (1 - 2 * γ) + 1) := by
            gcongr
        _ = 5 ^ (d - 1) * (2 * d * (δ⁻¹ * (R⁻¹ * (L ^ (d - 1) * L ^ (1 - 2 * γ)))) + L ^ (d - 1)) := by
            rw [h5L]; ring
        _ = 5 ^ (d - 1) * (2 * d * (δ⁻¹ * (R⁻¹ * L ^ ((d : ℝ) - 2 * γ))) + L ^ (d - 1)) := by rw [e1]
        _ ≤ 5 ^ d * (2 * d) * (L ^ (d - 1) + δ⁻¹ * (R⁻¹ * L ^ ((d : ℝ) - 2 * γ))) := by
            have hq : 0 ≤ δ⁻¹ * (R⁻¹ * L ^ ((d : ℝ) - 2 * γ)) := by positivity
            have : 0 ≤ (5 : ℝ) ^ (d - 1) := by positivity
            nlinarith [mul_le_mul_of_nonneg_right hpow (show 0 ≤ 2 * (d : ℝ) from by linarith),
              mul_nonneg this hq, mul_nonneg this hLp, pow_nonneg (show (0 : ℝ) ≤ 5 by norm_num) d]
    have hP2 : (((⌊2 * 2 * L⌋₊ + 1) ^ d : ℕ) : ℝ) ≤ 5 ^ d * (2 * d) * (L ^ (d - 1) + δ⁻¹ * L ^ d) := by
      push_cast
      calc ((⌊2 * 2 * L⌋₊ + 1 : ℝ)) ^ d ≤ (5 * L) ^ d := by
            gcongr
            exact_mod_cast hX2
        _ = 5 ^ d * L ^ d := mul_pow _ _ _
        _ ≤ 5 ^ d * (δ⁻¹ * L ^ d) := by
            have : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ).2 hδ1
            have h5 : 0 ≤ (5 : ℝ) ^ d * L ^ d := by positivity
            nlinarith
        _ ≤ _ := by
            have : 0 ≤ (5 : ℝ) ^ d * (δ⁻¹ * L ^ d) := by positivity
            have h2d : (1 : ℝ) ≤ 2 * d := by linarith
            have hLp : 0 ≤ L ^ (d - 1) := by positivity
            nlinarith [mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 5 by norm_num) d) hLp]
    rcases le_total (R⁻¹ * L ^ ((d : ℝ) - 2 * γ)) (L ^ d) with h | h
    · have : m = R⁻¹ * L ^ ((d : ℝ) - 2 * γ) := min_eq_left h
      rw [this]; exact (min_le_left _ _).trans hP1
    · have : m = L ^ d := min_eq_right h
      rw [this]; exact (min_le_right _ _).trans hP2
  unfold vineG
  rw [pow_zero]
  have hbase : (((⌊2 * 1 * L⌋₊ + 1) ^ d : ℕ) : ℝ) * (((⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) : ℝ) ≤
      3 ^ d * L ^ d * (3 ^ d * (ρ * L) ^ d) := by
    push_cast
    rw [← mul_pow, ← mul_pow]
    have : ((⌊2 * 1 * L⌋₊ : ℝ) + 1) ≤ 3 * L := by exact_mod_cast hX0
    have : ((⌊2 * ρ * L⌋₊ : ℝ) + 1) ≤ 3 * (ρ * L) := by exact_mod_cast hX1
    rw [← mul_pow, ← mul_pow]
    gcongr
  have hBnn : 0 ≤ min ((2 * (L * 2) + 1) ^ (d - 1) * (2 * (d : ℝ) * (δ⁻¹ * L ^ (-2 * γ) / 2) * L / (R / 2) + 1))
      (((⌊2 * 2 * L⌋₊ + 1) ^ d : ℕ) : ℝ) := le_min (by positivity) (by positivity)
  calc (((⌊2 * 1 * L⌋₊ + 1) ^ d : ℕ) : ℝ) * (((⌊2 * ρ * L⌋₊ + 1) ^ d : ℕ) : ℝ) *
        min ((2 * (L * 2) + 1) ^ (d - 1) * (2 * (d : ℝ) * (δ⁻¹ * L ^ (-2 * γ) / 2) * L / (R / 2) + 1))
          (((⌊2 * 2 * L⌋₊ + 1) ^ d : ℕ) : ℝ)
      ≤ (3 ^ d * L ^ d * (3 ^ d * (ρ * L) ^ d)) * (5 ^ d * (2 * d) * (L ^ (d - 1) + δ⁻¹ * m)) :=
        mul_le_mul hbase hB hBnn (by positivity)
    _ = _ := by
        have : (3 : ℝ) ^ d * 3 ^ d = 9 ^ d := by rw [← mul_pow]; norm_num
        calc _ = ((3 : ℝ) ^ d * 3 ^ d) * L ^ d * (ρ * L) ^ d * (5 ^ d * (2 * d) * (L ^ (d - 1) + δ⁻¹ * m)) := by ring
          _ = _ := by rw [this]; ring

end WaveTurbulence.FinalCount
