/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.OpDW2
public import WaveTurbulence.Foundations.FinalCount.G8R.CoreSplit
import Mathlib.Tactic

/-! # Arithmetic of the decoration-level split (finalcount-g8, F6-1)

The bound `A·(A·ε₁) + A·(C·ε₂) ≤ L^{-η_s/32}`, where `A = 21125 (log L)^14` is the constant of operation (d),
`C` that of operation (c), and `ε₁, ε₂` the sizes of `prop104_two_proved` at `η_s`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4

/-- The constant of the arithmetic bound. -/
noncomputable def splitK (d m : ℕ) (δ : ℝ) : ℝ :=
  21125 * (21125 + 2 * 3 ^ d * (d * δ⁻¹ + 1)) * 2750 ^ 2 * 2 ^ (m + 1)

theorem split_arith {d m : ℕ} {L γ δ ηs a : ℝ} (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hδ : 0 < δ) (hLe : Real.exp 1 ≤ L)
    (ha0 : 0 ≤ a) (ha : a ≤ (1 + Real.log L) ^ m)
    (hbig : splitK d m δ * Real.log L ^ (56 + m) ≤ L ^ (ηs / 32)) :
    21125 * Real.log L ^ (14 : ℝ) * (21125 * Real.log L ^ (14 : ℝ) *
        ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 * ((a + 1) * L ^ (-(ηs / 16))))) +
      21125 * Real.log L ^ (14 : ℝ) * (2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ (1 - γ) *
        ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
          ((a + 1) * L ^ (-(min γ (1 - γ) + ηs / 16))))) ≤ L ^ (-(ηs / 32)) := by
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  set ℓ := Real.log L with hℓ
  have hmin : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith)
  have h14 : ℓ ^ (14 : ℝ) = ℓ ^ 14 := by
    rw [show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h8 : ℓ ^ (8 : ℝ) = ℓ ^ 8 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hexp : L ^ (1 - γ) * L ^ (-(min γ (1 - γ) + ηs / 16)) = L ^ (-(ηs / 16)) := by
    rw [← Real.rpow_add hLp, hmin]; congr 1; ring
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hS : ((scaleSet L).card : ℝ) ≤ 5 * ℓ := card_scaleSet_le_log hlog
  have hS0 : (0 : ℝ) ≤ (scaleSet L).card := Nat.cast_nonneg _
  set Ks := (110 * ((scaleSet L).card : ℝ) ^ 2 * (ℓ ^ 2) ^ 6) ^ 2 with hKs
  have hKs0 : 0 ≤ Ks := sq_nonneg _
  have hKsle : Ks ≤ 2750 ^ 2 * ℓ ^ 28 := by
    have h1 : 110 * ((scaleSet L).card : ℝ) ^ 2 * (ℓ ^ 2) ^ 6 ≤ 2750 * ℓ ^ 14 := by
      have h2 : ((scaleSet L).card : ℝ) ^ 2 ≤ (5 * ℓ) ^ 2 := pow_le_pow_left₀ hS0 hS 2
      calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (ℓ ^ 2) ^ 6 ≤ 110 * (5 * ℓ) ^ 2 * (ℓ ^ 2) ^ 6 := by gcongr
        _ = 2750 * ℓ ^ 14 := by ring
    calc Ks ≤ (2750 * ℓ ^ 14) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = 2750 ^ 2 * ℓ ^ 28 := by ring
  have hbound : a + 1 ≤ 2 ^ (m + 1) * ℓ ^ m := by
    have h1 : (1 : ℝ) ≤ (1 + ℓ) ^ m := one_le_pow₀ (by linarith)
    have h2 : (1 + ℓ) ^ m ≤ (2 * ℓ) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    calc a + 1 ≤ (1 + ℓ) ^ m + 1 := by linarith
      _ ≤ 2 * (1 + ℓ) ^ m := by linarith
      _ ≤ 2 * (2 * ℓ) ^ m := by linarith
      _ = 2 ^ (m + 1) * ℓ ^ m := by rw [mul_pow, pow_succ]; ring
  have hc3 : 0 ≤ 2 * 3 ^ d * ((d : ℝ) * δ⁻¹ + 1) := by positivity
  set c3 := 2 * 3 ^ d * ((d : ℝ) * δ⁻¹ + 1) with hc3d
  rw [h14, h8]
  have hLm0 : 0 ≤ L ^ (-(ηs / 16)) := Real.rpow_nonneg hLp.le _
  have e : 21125 * ℓ ^ 14 * (21125 * ℓ ^ 14 * (Ks * ((a + 1) * L ^ (-(ηs / 16))))) +
      21125 * ℓ ^ 14 * (c3 * ℓ ^ 8 * L ^ (1 - γ) * (Ks * ((a + 1) * L ^ (-(min γ (1 - γ) + ηs / 16))))) =
      (21125 * ℓ ^ 14 * (21125 * ℓ ^ 14 + c3 * ℓ ^ 8) * Ks * (a + 1)) * L ^ (-(ηs / 16)) := by
    have h := hexp
    calc _ = 21125 * ℓ ^ 14 * (21125 * ℓ ^ 14 + c3 * ℓ ^ 8) * Ks * (a + 1) * (L ^ (1 - γ) * L ^ (-(min γ (1 - γ) + ηs / 16))) -
        21125 * ℓ ^ 14 * (21125 * ℓ ^ 14) * Ks * (a + 1) * (L ^ (1 - γ) * L ^ (-(min γ (1 - γ) + ηs / 16))) +
        21125 * ℓ ^ 14 * (21125 * ℓ ^ 14 * (Ks * ((a + 1) * L ^ (-(ηs / 16))))) := by ring
      _ = _ := by rw [h]; ring
  have h8le : ℓ ^ 8 ≤ ℓ ^ 14 := pow_le_pow_right₀ hlog (by norm_num)
  have hT : 21125 * ℓ ^ 14 * (21125 * ℓ ^ 14 + c3 * ℓ ^ 8) * Ks * (a + 1) ≤ splitK d m δ * ℓ ^ (56 + m) := by
    have hsum : 21125 * ℓ ^ 14 + c3 * ℓ ^ 8 ≤ (21125 + c3) * ℓ ^ 14 := by nlinarith
    calc 21125 * ℓ ^ 14 * (21125 * ℓ ^ 14 + c3 * ℓ ^ 8) * Ks * (a + 1)
        ≤ 21125 * ℓ ^ 14 * ((21125 + c3) * ℓ ^ 14) * (2750 ^ 2 * ℓ ^ 28) * (2 ^ (m + 1) * ℓ ^ m) := by
          have hp1 : 0 ≤ 21125 * ℓ ^ 14 + c3 * ℓ ^ 8 := by positivity
          have hp2 : 0 ≤ a + 1 := by linarith
          gcongr
      _ = splitK d m δ * ℓ ^ (56 + m) := by unfold splitK; rw [pow_add ℓ 56 m]; ring
  rw [e]
  calc _ ≤ (splitK d m δ * ℓ ^ (56 + m)) * L ^ (-(ηs / 16)) := mul_le_mul_of_nonneg_right hT hLm0
    _ ≤ L ^ (ηs / 32) * L ^ (-(ηs / 16)) := mul_le_mul_of_nonneg_right hbig hLm0
    _ = L ^ (-(ηs / 32)) := by rw [← Real.rpow_add hLp]; congr 1; ring

end WaveTurbulence.FinalCountG8
