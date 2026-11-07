/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Real-variable estimate for the bi-bridge deviation: `n L^{-(d-γ)} ≲ L^{γ₀}` -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FinalCountG8

theorem bibridge_n_bound {n L δ γ : ℝ} {d s : ℕ} (hL : 1 ≤ L) (hδ : 0 < δ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hd : 0 < d) (hn0 : 0 ≤ n)
    (hn : n ≤ min ((2 * L + 1) ^ d) ((2 * L + 1) ^ (d - 1) * (d * s * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2 + 1))) :
    n * L ^ (-((d : ℝ) - γ)) ≤ 3 ^ d * (d * δ⁻¹ + 1) * (s + 1) * L ^ (min γ (1 - γ)) := by
  have hLp : 0 < L := by linarith
  have h2L : 2 * L + 1 ≤ 3 * L := by linarith
  have hE : 0 < L ^ (-((d : ℝ) - γ)) := Real.rpow_pos_of_pos hLp _
  have hC1 : (1 : ℝ) ≤ (d * δ⁻¹ + 1) * (s + 1) := by
    have : (0 : ℝ) ≤ d * δ⁻¹ := by positivity
    have : (0 : ℝ) ≤ s := by positivity
    nlinarith
  have h3d : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have h3d1 : (3 : ℝ) ^ (d - 1) ≤ 3 ^ d := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  by_cases hcase : γ ≤ 1 - γ
  · rw [min_eq_left hcase]
    have ha : n ≤ (2 * L + 1) ^ d := hn.trans (min_le_left _ _)
    have hb : n ≤ (3 * L) ^ d := ha.trans (pow_le_pow_left₀ (by positivity) h2L d)
    have hLd : L ^ (d : ℝ) * L ^ (-((d : ℝ) - γ)) = L ^ γ := by
      rw [← Real.rpow_add hLp]; congr 1; ring
    calc n * L ^ (-((d : ℝ) - γ)) ≤ (3 * L) ^ d * L ^ (-((d : ℝ) - γ)) :=
          mul_le_mul_of_nonneg_right hb hE.le
      _ = 3 ^ d * (L ^ (d : ℝ) * L ^ (-((d : ℝ) - γ))) := by
          rw [mul_pow, Real.rpow_natCast]; ring
      _ = 3 ^ d * L ^ γ := by rw [hLd]
      _ ≤ 3 ^ d * ((d * δ⁻¹ + 1) * (s + 1)) * L ^ γ := by
          have : 0 ≤ L ^ γ := Real.rpow_nonneg hLp.le _
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 3 ^ d) this]
      _ = _ := by ring
  · push Not at hcase
    rw [min_eq_right hcase.le]
    have hb : n ≤ (2 * L + 1) ^ (d - 1) * (d * s * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2 + 1) :=
      hn.trans (min_le_right _ _)
    have hexp : (0 : ℝ) ≤ 2 - 2 * γ := by linarith
    have hone : (1 : ℝ) ≤ L ^ (2 - 2 * γ) := Real.one_le_rpow hL hexp
    have hτ : δ⁻¹ * L ^ (-2 * γ) * L ^ 2 = δ⁻¹ * L ^ (2 - 2 * γ) := by
      rw [mul_assoc]; congr 1
      rw [show (L ^ 2 : ℝ) = L ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hLp]; congr 1; ring
    have hX : (d : ℝ) * s * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2 + 1 ≤ ((d : ℝ) * δ⁻¹ * s + 1) * L ^ (2 - 2 * γ) := by
      have : (d : ℝ) * s * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2 = (d : ℝ) * s * (δ⁻¹ * L ^ (-2 * γ) * L ^ 2) := by ring
      rw [this, hτ]
      nlinarith [hone]
    have hLd : L ^ ((d - 1 : ℕ) : ℝ) * L ^ (2 - 2 * γ) * L ^ (-((d : ℝ) - γ)) = L ^ (1 - γ) := by
      rw [← Real.rpow_add hLp, ← Real.rpow_add hLp]
      congr 1
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      push_cast; ring
    have h3 : (2 * L + 1) ^ (d - 1) ≤ (3 * L) ^ (d - 1) := pow_le_pow_left₀ (by positivity) h2L _
    have hpos : 0 ≤ (d : ℝ) * s * (δ⁻¹ * L ^ (-2 * γ)) * L ^ 2 + 1 := by positivity
    calc n * L ^ (-((d : ℝ) - γ)) ≤ ((3 * L) ^ (d - 1) * (((d : ℝ) * δ⁻¹ * s + 1) * L ^ (2 - 2 * γ))) *
          L ^ (-((d : ℝ) - γ)) := by
          refine mul_le_mul_of_nonneg_right (hb.trans ?_) hE.le
          exact mul_le_mul h3 hX hpos (by positivity)
      _ = 3 ^ (d - 1) * ((d * δ⁻¹ * s + 1)) *
          (L ^ ((d - 1 : ℕ) : ℝ) * L ^ (2 - 2 * γ) * L ^ (-((d : ℝ) - γ))) := by
          rw [mul_pow, Real.rpow_natCast]; ring
      _ = 3 ^ (d - 1) * ((d * δ⁻¹ * s + 1)) * L ^ (1 - γ) := by rw [hLd]
      _ ≤ 3 ^ d * ((d * δ⁻¹ + 1) * (s + 1)) * L ^ (1 - γ) := by
          have : 0 ≤ L ^ (1 - γ) := Real.rpow_nonneg hLp.le _
          have h4 : (d * δ⁻¹ * s + 1 : ℝ) ≤ (d * δ⁻¹ + 1) * (s + 1) := by
            have : (0 : ℝ) ≤ d * δ⁻¹ := by positivity
            have : (0 : ℝ) ≤ s := by positivity
            nlinarith
          have h5 : (3 : ℝ) ^ (d - 1) * (d * δ⁻¹ * s + 1) ≤ 3 ^ d * ((d * δ⁻¹ + 1) * (s + 1)) :=
            mul_le_mul h3d1 h4 (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right h5 this
      _ = _ := by ring

end WaveTurbulence.FinalCountG8
