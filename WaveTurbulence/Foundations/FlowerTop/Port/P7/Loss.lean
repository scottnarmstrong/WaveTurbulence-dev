/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Trunc
public import WaveTurbulence.Foundations.Spine.NonregularNumericsP
/-! FLOWER-P7: the data counts are polylogarithmic in `L`, so the loss hypothesis of `coupleSum_true_bound` is a
numerical condition `const · (log L)^{12 logExp} ≤ L^{94d - 6}`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open WaveTurbulence.Induct
open TTree Finset LGSpine

theorem Qn_le (P : WTParams) (hd : 1 ≤ P.d) (hlog : 1 ≤ Real.log P.L) (p N : ℕ) (hN : N ≤ P.N (p + 1) ^ 4)
    {Cr : ℝ} (hC : 0 ≤ Cr) :
    Qn P p N Cr ≤ (2 * Real.log P.L ^ logExp P) ^ 12 * (1 + Cr) ^ 3 := by
  set Z : ℝ := Real.log P.L ^ logExp P with hZ
  have hZ1 : 1 ≤ Z := one_le_pow₀ hlog
  have hM4 := N_quartic_le_log_pow P hd hlog (p + 1)
  have hM4' : ((P.N (p + 1) : ℕ) : ℝ) ^ 4 ≤ Z := by rw [hZ]; exact hM4
  have hMZ : ((P.N (p + 1) : ℕ) : ℝ) ≤ Z := by
    refine le_trans ?_ hM4'
    rcases Nat.eq_zero_or_pos (P.N (p + 1)) with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ ((P.N (p + 1) : ℕ) : ℝ) := by exact_mod_cast h
      nlinarith [pow_le_pow_right₀ this (show 1 ≤ 4 by norm_num)]
  have hNZ : (N : ℝ) ≤ Z := by
    refine le_trans ?_ hM4'
    exact_mod_cast hN
  have h1 : ((N : ℝ) + 1) ≤ 2 * Z := by linarith
  have h2 : (((P.N (p + 1) : ℕ) : ℝ) + 1) ≤ 2 * Z := by linarith
  have h0 : (0 : ℝ) ≤ (P.N (p + 1) : ℝ) + 1 := by positivity
  unfold Qn
  push_cast
  have e : (2 * Z) ^ 12 = (2 * Z) * (2 * Z) ^ 6 * ((2 * Z) * (2 * Z) ^ 4) := by ring
  rw [e]
  have hq : ((N : ℝ) + 1) * (((P.N (p + 1) : ℕ) : ℝ) + 1) ^ 6 ≤ (2 * Z) * (2 * Z) ^ 6 :=
    mul_le_mul h1 (pow_le_pow_left₀ h0 h2 6) (by positivity) (by positivity)
  have hq' : ((N : ℝ) + 1) * (((P.N (p + 1) : ℕ) : ℝ) + 1) ^ 4 ≤ (2 * Z) * (2 * Z) ^ 4 :=
    mul_le_mul h1 (pow_le_pow_left₀ h0 h2 4) (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul hq hq' (by positivity) (by positivity)) (by positivity)

theorem hLoss_of_numerics (P : WTParams) (hd : 1 ≤ P.d) (hlog : 1 ≤ Real.log P.L) (hL : 1 ≤ P.L) (p N : ℕ)
    (hN : N ≤ P.N (p + 1) ^ 4) {Cr : ℝ} (hC : 0 ≤ Cr)
    (hE : (12 * 2 ^ 12 * (1 + Cr) ^ 3 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * Kd P.d ^ 6) *
        Real.log P.L ^ (12 * logExp P) ≤ P.L ^ ((100 * P.d : ℝ) - 6 * ((P.d : ℝ) + 1))) :
    Qn P p N Cr * 12 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * (Kd P.d * P.L ^ (P.d + 1)) ^ 6 ≤
      P.L ^ (100 * P.d : ℝ) := by
  have hL0 : 0 < P.L := by linarith
  have hQ := Qn_le P hd hlog p N hN hC
  have h3 : (0 : ℝ) ≤ 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hK : (0 : ℝ) ≤ Kd P.d := by linarith [one_le_Kd P.d]
  have hLp : (P.L ^ (P.d + 1)) ^ 6 = P.L ^ (6 * ((P.d : ℝ) + 1)) := by
    rw [← pow_mul, ← Real.rpow_natCast]
    congr 1; push_cast; ring
  calc Qn P p N Cr * 12 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * (Kd P.d * P.L ^ (P.d + 1)) ^ 6
      ≤ ((2 * Real.log P.L ^ logExp P) ^ 12 * (1 + Cr) ^ 3) * 12 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) *
          (Kd P.d * P.L ^ (P.d + 1)) ^ 6 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQ (by norm_num)) h3
    _ = (12 * 2 ^ 12 * (1 + Cr) ^ 3 * 3 ^ (4 * (P.Lambda (p + 1) : ℝ)) * Kd P.d ^ 6) *
          Real.log P.L ^ (12 * logExp P) * P.L ^ (6 * ((P.d : ℝ) + 1)) := by
        rw [mul_pow (Kd P.d), hLp, mul_pow 2, ← pow_mul]
        rw [mul_comm (logExp P) 12]
        ring
    _ ≤ P.L ^ ((100 * P.d : ℝ) - 6 * ((P.d : ℝ) + 1)) * P.L ^ (6 * ((P.d : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hE (Real.rpow_nonneg hL0.le _)
    _ = P.L ^ (100 * P.d : ℝ) := by
        rw [← Real.rpow_add hL0]; congr 1; ring

end WaveTurbulence.FlowerP7
