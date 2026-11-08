/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib

/-! # D6b: `δ^{n/2}` versus `δ^{7νn}` (copied by source from D0-PROT `probe/RegProbe.lean`, see COPIED-SHA256SUMS)

A regular couple of garden order `n ≥ 1` has the natural bound `C^{n+1} δ^{n/2}`; for `ν ≤ 1/28` and `δ ≤ C^{-8}` it is
at most `δ^{7νn}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.Flower.ProtWhole

theorem regular_delta_absorb (C δ ν : ℝ) (n : ℕ) (hn : 1 ≤ n) (hC : 1 ≤ C) (hδ0 : 0 < δ)
    (hδC : δ ≤ (C ^ 8)⁻¹) (_hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 28) :
    C ^ (n + 1) * δ ^ ((n : ℝ) / 2) ≤ δ ^ (7 * ν * n) := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hC8 : 1 ≤ C ^ 8 := one_le_pow₀ hC
  have hδ1 : δ ≤ 1 := hδC.trans (inv_le_one_of_one_le₀ hC8)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- δ^{n/2} ≤ δ^{7νn} · δ^{n/4}
  have hexp : 7 * ν * n + n / 4 ≤ (n : ℝ) / 2 := by nlinarith
  have h1 : δ ^ ((n : ℝ) / 2) ≤ δ ^ (7 * ν * n + n / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hexp
  rw [Real.rpow_add hδ0] at h1
  -- δ^{n/4} = (δ^{1/4})^n ≤ (C^{-2})^n
  have hq : δ ^ ((n : ℝ) / 4) = (δ ^ ((1 : ℝ) / 4)) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ0.le]
    congr 1
    ring
  have hroot : δ ^ ((1 : ℝ) / 4) ≤ (C ^ 2)⁻¹ := by
    have h8 : (C ^ 8)⁻¹ = ((C ^ 2)⁻¹) ^ (4 : ℝ) := by
      rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow, ← pow_mul]
    have hpos : 0 ≤ (C ^ 2)⁻¹ := by positivity
    calc δ ^ ((1 : ℝ) / 4) ≤ ((C ^ 8)⁻¹) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow hδ0.le hδC (by norm_num)
      _ = (C ^ 2)⁻¹ := by
          rw [h8, ← Real.rpow_mul hpos]
          norm_num
  have hd4 : δ ^ ((n : ℝ) / 4) ≤ ((C ^ 2)⁻¹) ^ n := by
    rw [hq]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hδ0.le _) hroot n
  have hCn : C ^ (n + 1) ≤ C ^ (2 * n) := pow_le_pow_right₀ hC (by omega)
  have hkey : C ^ (n + 1) * δ ^ ((n : ℝ) / 4) ≤ 1 := by
    calc C ^ (n + 1) * δ ^ ((n : ℝ) / 4) ≤ C ^ (2 * n) * ((C ^ 2)⁻¹) ^ n :=
          mul_le_mul hCn hd4 (Real.rpow_nonneg hδ0.le _) (by positivity)
      _ = 1 := by
          rw [inv_pow, ← pow_mul, mul_inv_cancel₀ (pow_ne_zero _ hC0.ne')]
  have hA : 0 ≤ δ ^ (7 * ν * n) := Real.rpow_nonneg hδ0.le _
  calc C ^ (n + 1) * δ ^ ((n : ℝ) / 2)
      ≤ C ^ (n + 1) * (δ ^ (7 * ν * n) * δ ^ ((n : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = δ ^ (7 * ν * n) * (C ^ (n + 1) * δ ^ ((n : ℝ) / 4)) := by ring
    _ ≤ δ ^ (7 * ν * n) * 1 := mul_le_mul_of_nonneg_left hkey hA
    _ = δ ^ (7 * ν * n) := mul_one _

end WaveTurbulence.Flower.ProtWhole
