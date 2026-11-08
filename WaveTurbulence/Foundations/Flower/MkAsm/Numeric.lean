/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkAsm.Budget

/-! # A5 MK-ASM: numerics. The structure count `(4Pm)^{4Pm}(N+1)^{4Pm} 2^{Pm}` is absorbed by `L^{4000 d Pm}` once
`L` is large, because `N ≤ N_{p+1}^4` is a power of `log L` (polylogarithmic in `L`, depending on `d` and `D`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence Finset Filter Asymptotics

namespace WaveTurbulence.Flower.MkAsm

/-- Exponents of the `log L` bound for `Rdown`. -/
def eRd (d : ℕ) : ℕ → ℕ
  | 0 => 40 * d
  | k + 1 => eRd d k * (40 * d) * (40 * d)

theorem Rdown_le (P : WTParams) (hx : 1 ≤ Real.log P.L) (k : ℕ) :
    (P.Rdown k : ℝ) ≤ (Real.log P.L) ^ (eRd P.d k) := by
  induction k with
  | zero =>
    simp only [WTParams.Rdown, eRd]
    exact Nat.floor_le (by positivity)
  | succ k ih =>
    simp only [WTParams.Rdown, eRd]
    push_cast
    calc ((P.Rdown k : ℝ) ^ (40 * P.d)) ^ (40 * P.d)
        ≤ (((Real.log P.L) ^ (eRd P.d k)) ^ (40 * P.d)) ^ (40 * P.d) := by
          gcongr
      _ = (Real.log P.L) ^ (eRd P.d k * (40 * P.d) * (40 * P.d)) := by
          rw [← pow_mul, ← pow_mul]; congr 1; ring

/-- `P.N q ≤ (log L)^(E d D · 40 d)` for `q ≥ 0`, with `E d D = ∑_{k ≤ D} eRd d k`. -/
theorem N_le (P : WTParams) (hx : 1 ≤ Real.log P.L) (q : ℕ) :
    (P.N q : ℝ) ≤ (Real.log P.L) ^ ((∑ k ∈ range (P.D + 1), eRd P.d k) * (40 * P.d)) := by
  have hk : P.D - q ∈ range (P.D + 1) := by simp only [Finset.mem_range]; omega
  have h1 : (P.R q : ℝ) ≤ (Real.log P.L) ^ (∑ k ∈ range (P.D + 1), eRd P.d k) := by
    refine (Rdown_le P hx _).trans ?_
    refine pow_le_pow_right₀ hx ?_
    exact Finset.single_le_sum (f := fun k => eRd P.d k) (fun _ _ => Nat.zero_le _) hk
  unfold WTParams.N
  push_cast
  calc ((P.R q : ℝ)) ^ (40 * P.d) ≤ ((Real.log P.L) ^ (∑ k ∈ range (P.D + 1), eRd P.d k)) ^ (40 * P.d) := by
        gcongr
    _ = _ := by rw [← pow_mul]

/-- The absorption threshold: for all large `L`, the structure count is at most `L^{4000 d Pm}` (exponent `4Pm` on
`N + 1`, which covers both the F count `(N+1)^{2Pm}` and the G count with stem-depth labels, ruling R156 (3)). -/
theorem exists_threshold (d D Pm : ℕ) (hPm : 1 ≤ Pm) (hd : 1 ≤ d) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ P : WTParams, P.d = d → P.D = D → L₀ ≤ P.L →
      ∀ p : ℕ, ∀ N : ℕ, N ≤ P.N (p + 1) ^ 4 →
        ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) * 2 ^ Pm ≤ (P.L ^ (4000 * d)) ^ Pm := by
  set E : ℕ := (∑ k ∈ range (D + 1), eRd d k) * (40 * d) * 4 with hE
  set M : ℕ := 4 * E * Pm with hM
  set C : ℝ := ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * 16 ^ Pm * 2 ^ Pm with hC
  have hCpos : 0 < C := by
    have : (0 : ℝ) < ((4 * Pm : ℕ) : ℝ) := by positivity
    positivity
  have hlo := (Real.isLittleO_pow_log_id_atTop (n := M)).bound (c := C⁻¹) (by positivity)
  rw [Filter.eventually_atTop] at hlo
  obtain ⟨a, ha⟩ := hlo
  refine ⟨max (max a 3) 3, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro P hPd hPD hL p N hN
  have hLa : a ≤ P.L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL3 : 3 ≤ P.L := le_trans (le_max_right _ _) hL
  have hx : 1 ≤ Real.log P.L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hL1 : 1 ≤ P.L := by linarith
  -- polylog bound of N + 1
  have hN1 : ((N : ℝ) + 1) ≤ 2 * (Real.log P.L) ^ E := by
    have h1 : (N : ℝ) ≤ ((P.N (p + 1) : ℝ)) ^ 4 := by exact_mod_cast hN
    have h2 := N_le P hx (p + 1)
    rw [hPd, hPD] at h2
    have h3 : ((P.N (p + 1) : ℝ)) ^ 4 ≤ (Real.log P.L) ^ E := by
      calc ((P.N (p + 1) : ℝ)) ^ 4
          ≤ ((Real.log P.L) ^ ((∑ k ∈ range (D + 1), eRd d k) * (40 * d))) ^ 4 := by
            rw [hPd, hPD] at *
            gcongr
        _ = _ := by rw [hE, ← pow_mul]
    have h4 : (1 : ℝ) ≤ (Real.log P.L) ^ E := one_le_pow₀ hx
    linarith
  have hmain : C * (Real.log P.L) ^ M ≤ P.L := by
    have := ha P.L hLa
    simp only [id, Real.norm_eq_abs] at this
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)] at this
    have h5 : (Real.log P.L) ^ M ≤ C⁻¹ * P.L := this
    calc C * (Real.log P.L) ^ M ≤ C * (C⁻¹ * P.L) := by gcongr
      _ = P.L := by field_simp
  have hpow : (4000 * d : ℕ) * Pm ≥ 1 := by
    have : 1 ≤ 4000 * d := by omega
    nlinarith
  calc ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) * 2 ^ Pm
      ≤ ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * (2 * (Real.log P.L) ^ E) ^ (4 * Pm) * 2 ^ Pm := by gcongr
    _ = C * (Real.log P.L) ^ M := by
        rw [mul_pow, ← pow_mul, hC, hM]
        have : (2 : ℝ) ^ (4 * Pm) = 16 ^ Pm := by rw [pow_mul]; norm_num
        rw [this]; ring_nf
    _ ≤ P.L := hmain
    _ ≤ P.L ^ ((4000 * d) * Pm) := by
        calc P.L = P.L ^ 1 := (pow_one _).symm
          _ ≤ _ := pow_le_pow_right₀ hL1 hpow
    _ = (P.L ^ (4000 * d)) ^ Pm := by rw [pow_mul]

end WaveTurbulence.Flower.MkAsm
