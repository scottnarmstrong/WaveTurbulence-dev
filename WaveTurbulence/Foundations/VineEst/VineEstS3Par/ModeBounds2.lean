/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ModeBounds

/-! # The per-mode weight (engine step ASM)

`2^{θ_a} ⟨ν_m/2⟩^{θ_a} (maxPar D_m)^{η⁶} ≤ C₀ C^{|Row|} (maxPar D)^{η⁶} ∏_ρ ⟨m_ρ/2⟩^{6η⁶}` for `θ_a = 2η⁸ ≤ 2η⁶`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3Par.Eng
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS Finset
open scoped ENNReal

variable {d : ℕ} (D : SumintPar.SumintDatum d)

theorem maxPar_shift_le (slot : Row D → Fin 2 → Slot D) (m : Row D → Fin 2 → ℤ) :
    maxPar { D with param := fun v => D.param v + modeParam D slot m v } ≤
      Real.sqrt 2 * maxPar D * (Real.sqrt 2 ^ (2 * Fintype.card (Row D)) *
        (4 ^ Fintype.card (Row D) * (∏ ρ, modeBr D m ρ) ^ 2)) := by
  rw [maxPar_eq, maxPar_eq]
  have hX : 0 ≤ Real.sqrt 2 * (⨆ v, WaveTurbulence.VineEstS3.Eng.Jb (D.param v)) * (Real.sqrt 2 ^ (2 * Fintype.card (Row D)) *
        (4 ^ Fintype.card (Row D) * (∏ ρ, modeBr D m ρ) ^ 2)) := by
    have h0 : 0 ≤ ⨆ v, WaveTurbulence.VineEstS3.Eng.Jb (D.param v) := Real.iSup_nonneg fun v => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le
    positivity
  refine Real.iSup_le (fun v => ?_) hX
  have h1 := WaveTurbulence.VineEstS3.Eng.Jb_add_le (D.param v) (modeParam D slot m v)
  have h2 := Jb_modeParam_le D slot m v
  have h3 : WaveTurbulence.VineEstS3.Eng.Jb (D.param v) ≤ ⨆ v, WaveTurbulence.VineEstS3.Eng.Jb (D.param v) := le_ciSup (f := fun v => WaveTurbulence.VineEstS3.Eng.Jb (D.param v)) (Finite.bddAbove_range _) v
  have h4 : ∏ ρ, (2 * modeBr D m ρ) ^ 2 = 4 ^ Fintype.card (Row D) * (∏ ρ, modeBr D m ρ) ^ 2 := by
    have : ∀ ρ : Row D, (2 * modeBr D m ρ) ^ 2 = 4 * modeBr D m ρ ^ 2 := fun ρ => by ring
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
  rw [h4] at h2
  calc WaveTurbulence.VineEstS3.Eng.Jb (D.param v + modeParam D slot m v) ≤ Real.sqrt 2 * WaveTurbulence.VineEstS3.Eng.Jb (D.param v) * WaveTurbulence.VineEstS3.Eng.Jb (modeParam D slot m v) := h1
    _ ≤ Real.sqrt 2 * (⨆ v, WaveTurbulence.VineEstS3.Eng.Jb (D.param v)) * (Real.sqrt 2 ^ (2 * Fintype.card (Row D)) *
        (4 ^ Fintype.card (Row D) * (∏ ρ, modeBr D m ρ) ^ 2)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)) h2 (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le
          (mul_nonneg (Real.sqrt_nonneg _) (le_trans (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le h3))


theorem rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (s : ℝ) : (x ^ n) ^ s = (x ^ s) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx, Real.rpow_natCast]

theorem sqrt_two_pow_two_mul (K : ℕ) : Real.sqrt 2 ^ (2 * K) = 2 ^ K := by
  rw [pow_mul, Real.sq_sqrt (by norm_num)]

/-- **The per-mode weight (real form).** -/
theorem mode_real_bound {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (slot : Row D → Fin 2 → Slot D)
    (m : Row D → Fin 2 → ℤ) :
    (2 : ℝ) ^ (2 * η ^ 8) * (timeBracket fun c => modeFreq D slot m c / 2) ^ (2 * η ^ 8) *
        (maxPar { D with param := fun v => D.param v + modeParam D slot m v }) ^ (η ^ 6) ≤
      ((2 : ℝ) ^ (2 * η ^ 8) * Real.sqrt 2 ^ (η ^ 6)) *
        ((2 : ℝ) ^ (2 * η ^ 8 + η ^ 6) * 4 ^ (η ^ 6)) ^ Fintype.card (Row D) *
        (maxPar D) ^ (η ^ 6) * ∏ ρ, modeBr D m ρ ^ (6 * η ^ 6) := by
  set K := Fintype.card (Row D) with hK
  set X := ∏ ρ, modeBr D m ρ with hXdef
  have hX1 : 1 ≤ X := one_le_prod_real _ fun ρ => one_le_modeBr D m ρ
  have hθa : 0 ≤ 2 * η ^ 8 := by positivity
  have hpp : 0 ≤ η ^ 6 := by positivity
  have hmP : 0 ≤ maxPar D := by rw [maxPar_eq]; exact Real.iSup_nonneg fun v => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le
  have h_tb : (timeBracket fun c => modeFreq D slot m c / 2) ≤ 2 ^ K * X ^ 2 := by
    have := timeBracket_modeFreq_le D slot m
    rwa [sqrt_two_pow_two_mul, Finset.prod_pow] at this
  have h_mp : maxPar { D with param := fun v => D.param v + modeParam D slot m v } ≤
      Real.sqrt 2 * maxPar D * (2 ^ K * (4 ^ K * X ^ 2)) := by
    have := maxPar_shift_le D slot m
    rwa [sqrt_two_pow_two_mul] at this
  have hb0 : 0 ≤ timeBracket fun c => modeFreq D slot m c / 2 := (timeBracket_pos _).le
  have hP0 : 0 ≤ maxPar { D with param := fun v => D.param v + modeParam D slot m v } := by
    rw [maxPar_eq]; exact Real.iSup_nonneg fun v => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le
  have e1 := Real.rpow_le_rpow hb0 h_tb hθa
  have e2 := Real.rpow_le_rpow hP0 h_mp hpp
  have hX0 : 0 ≤ X := le_trans zero_le_one hX1
  have hsq : ∀ s : ℝ, (X ^ 2) ^ s = X ^ (2 * s) := by
    intro s
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
    norm_num
  have hA1 : (2 ^ K * X ^ 2 : ℝ) ^ (2 * η ^ 8) = ((2 : ℝ) ^ (2 * η ^ 8)) ^ K * X ^ (2 * (2 * η ^ 8)) := by
    rw [Real.mul_rpow (by positivity) (by positivity), rpow_pow_comm (by norm_num), hsq]
  have hA2 : (Real.sqrt 2 * maxPar D * (2 ^ K * (4 ^ K * X ^ 2)) : ℝ) ^ (η ^ 6) =
      Real.sqrt 2 ^ (η ^ 6) * maxPar D ^ (η ^ 6) *
        (((2 : ℝ) ^ (η ^ 6)) ^ K * (((4 : ℝ) ^ (η ^ 6)) ^ K * X ^ (2 * η ^ 6))) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hmP,
      Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      rpow_pow_comm (by norm_num), rpow_pow_comm (by norm_num), hsq]
  have hexp : X ^ (2 * (2 * η ^ 8)) * X ^ (2 * η ^ 6) ≤ X ^ (6 * η ^ 6) := by
    rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hX1)]
    refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
    have : η ^ 8 ≤ η ^ 6 := pow_le_pow_of_le_one hη0 hη1 (by norm_num)
    nlinarith
  have hprodX : ∏ ρ, modeBr D m ρ ^ (6 * η ^ 6) = X ^ (6 * η ^ 6) := by
    rw [hXdef, Real.finset_prod_rpow]
    intro ρ _
    exact (lt_of_lt_of_le zero_lt_one (one_le_modeBr D m ρ)).le
  rw [hprodX]
  have hc : (((2 : ℝ) ^ (2 * η ^ 8 + η ^ 6)) * 4 ^ (η ^ 6)) ^ K =
      ((2 : ℝ) ^ (2 * η ^ 8)) ^ K * ((2 : ℝ) ^ (η ^ 6)) ^ K * ((4 : ℝ) ^ (η ^ 6)) ^ K := by
    rw [mul_pow, Real.rpow_add (by norm_num), mul_pow]
  rw [hc]
  calc (2 : ℝ) ^ (2 * η ^ 8) * (timeBracket fun c => modeFreq D slot m c / 2) ^ (2 * η ^ 8) *
        (maxPar { D with param := fun v => D.param v + modeParam D slot m v }) ^ (η ^ 6)
      ≤ (2 : ℝ) ^ (2 * η ^ 8) * (2 ^ K * X ^ 2 : ℝ) ^ (2 * η ^ 8) *
        (Real.sqrt 2 * maxPar D * (2 ^ K * (4 ^ K * X ^ 2)) : ℝ) ^ (η ^ 6) := by
        gcongr
    _ = ((2 : ℝ) ^ (2 * η ^ 8) * Real.sqrt 2 ^ (η ^ 6)) *
          (((2 : ℝ) ^ (2 * η ^ 8)) ^ K * ((2 : ℝ) ^ (η ^ 6)) ^ K * ((4 : ℝ) ^ (η ^ 6)) ^ K) *
          maxPar D ^ (η ^ 6) * (X ^ (2 * (2 * η ^ 8)) * X ^ (2 * η ^ 6)) := by
        rw [hA1, hA2]; ring
    _ ≤ _ := by
        gcongr

end WaveTurbulence.VineEstS3Par.Eng
