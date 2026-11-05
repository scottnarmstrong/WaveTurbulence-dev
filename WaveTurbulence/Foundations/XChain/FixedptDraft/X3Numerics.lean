/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Event
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Params

/-!
# X3: the numerical conditions of `fixedpoint` for large `L`

With `N = N_{p+1} ≥ 100 d log L + 10` (`N_ge_log`) and `M = L^{100d} ≤ e^{N}`:
- `part1Bound_le`: `part1Bound ≤ e^{-4N}/2` once `L ≥ 16·2^{d+1}·S_d`;
- `triK_le`: `triK ≤ e^{4N}/18` once `L ≥ 18·3^{Λ+1}·4^{d+1}·S_d²`.

Here `S_d = ∑_m (1+|m|)^{-(d+1)}`, so that `T ≤ (√2 L)^{d+1} S_d` (`latSum_le`).
-/

@[expose] public section

namespace WaveTurbulence.Fixedpt

open Set

/-- `S_d = ∑_m (1+|m|)^{-(d+1)}`. -/
noncomputable def latConst (d : ℕ) : ℝ := ∑' m : Fin d → ℤ, ((1 + ‖m‖) ^ (d + 1))⁻¹

theorem latConst_nonneg (d : ℕ) : 0 ≤ latConst d :=
  tsum_nonneg fun _ => inv_nonneg.2 (pow_nonneg (by positivity) _)

theorem latSum_le' {d : ℕ} {L : ℝ} (hL : 1 ≤ L) : latSum d L ≤ 2 ^ (d + 1) * L ^ (d + 1) * latConst d := by
  refine (latSum_le hL).trans ?_
  have hS := latConst_nonneg d
  have h2 : Real.sqrt 2 * L ≤ 2 * L := by
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith
  have h0 : 0 ≤ Real.sqrt 2 * L := by positivity
  calc (Real.sqrt 2 * L) ^ (d + 1) * latConst d ≤ (2 * L) ^ (d + 1) * latConst d := by
        gcongr
    _ = _ := by rw [mul_pow]

/-- `e^{N} ≥ e^{10} L^{100d}`. -/
theorem exp_N_ge (P : WTParams) (hd : 1 ≤ P.d) (hL : Real.exp (100 * P.d + 11) ≤ P.L) (q : ℕ) :
    Real.exp 10 * P.L ^ (100 * P.d : ℝ) ≤ Real.exp (P.N q : ℝ) := by
  have hLpos : 0 < P.L := (Real.exp_pos _).trans_le hL
  have h := WTParams.N_ge_log P hd hL q
  calc Real.exp 10 * P.L ^ (100 * P.d : ℝ) = Real.exp (100 * P.d * Real.log P.L + 10) := by
        rw [Real.rpow_def_of_pos hLpos, ← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (P.N q : ℝ) := Real.exp_le_exp.2 h

theorem rpow_ge_pow {L : ℝ} (hL : 1 ≤ L) {k : ℕ} {r : ℝ} (hk : (k : ℝ) ≤ r) : L ^ k ≤ L ^ r := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hL hk

theorem part1Bound_le (P : WTParams) (p : ℕ) (hd : 1 ≤ P.d) (hL : Real.exp (100 * P.d + 11) ≤ P.L)
    (hL2 : 16 * 2 ^ (P.d + 1) * latConst P.d ≤ P.L) :
    part1Bound P p ≤ Real.exp (-(4 * P.N (p + 1) : ℝ)) / 2 := by
  have hL1 : 1 ≤ P.L := le_trans (Real.one_le_exp (by positivity)) hL
  have hL0 : 0 ≤ P.L := by linarith
  set N : ℝ := (P.N (p + 1) : ℝ)
  set M : ℝ := P.L ^ (100 * P.d : ℝ)
  have hM1 : 1 ≤ M := Real.one_le_rpow hL1 (by positivity)
  have hEN := exp_N_ge P hd hL (p + 1)
  have hE10 : 1 ≤ Real.exp 10 := Real.one_le_exp (by norm_num)
  have hMN : M ≤ Real.exp N := le_trans (le_mul_of_one_le_left (by linarith) hE10) hEN
  have hS := latConst_nonneg P.d
  have hT := latSum_le' (d := P.d) hL1
  have hT0 : 0 ≤ latSum P.d P.L := tsum_nonneg fun _ => Real.rpow_nonneg (jbr_pos'' _).le _
  -- `M ≥ L^{d+3} · L`
  have hMd : P.L ^ (P.d + 3) * P.L ≤ M := by
    rw [← pow_succ]
    exact rpow_ge_pow hL1 (by push_cast; nlinarith [(Nat.one_le_cast (α := ℝ)).2 hd])
  have hX6 : Real.exp (3 * N) ^ 2 = Real.exp (2 * N) * Real.exp (4 * N) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have h2N : M * M ≤ Real.exp (2 * N) := by
    rw [show 2 * N = N + N by ring, Real.exp_add]
    exact mul_le_mul hMN hMN (by linarith) (Real.exp_pos _).le
  have hfac : 2 * (P.L ^ 2 * Real.exp (-(100 * N))) * (1 + M) / Real.exp (-(20 * N)) ^ 2 ≤
      2 * P.L ^ 2 * (1 + M) / Real.exp (3 * N) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    have : Real.exp (-(100 * N)) * Real.exp (((2 : ℕ) : ℝ) * (3 * N)) ≤ Real.exp (((2 : ℕ) : ℝ) * -(20 * N)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by push_cast; nlinarith [(Nat.cast_nonneg (P.N (p + 1)) : (0 : ℝ) ≤ N)])
    have hp : 0 ≤ 2 * P.L ^ 2 * (1 + M) := by positivity
    calc 2 * (P.L ^ 2 * Real.exp (-(100 * N))) * (1 + M) * Real.exp (((2 : ℕ) : ℝ) * (3 * N))
        = 2 * P.L ^ 2 * (1 + M) * (Real.exp (-(100 * N)) * Real.exp (((2 : ℕ) : ℝ) * (3 * N))) := by ring
      _ ≤ 2 * P.L ^ 2 * (1 + M) * Real.exp (((2 : ℕ) : ℝ) * -(20 * N)) := by gcongr
  unfold part1Bound
  calc (2 * P.L ^ 2 * (1 + P.L ^ (100 * P.d : ℝ)) / Real.exp (3 * N) ^ 2 +
        2 * (P.L ^ 2 * Real.exp (-(100 * N))) * (1 + P.L ^ (100 * P.d : ℝ)) / Real.exp (-(20 * N)) ^ 2) *
          latSum P.d P.L
      ≤ (2 * (2 * P.L ^ 2 * (1 + M) / Real.exp (3 * N) ^ 2)) * (2 ^ (P.d + 1) * P.L ^ (P.d + 1) * latConst P.d) := by
        gcongr
        linarith
    _ ≤ (2 * (2 * P.L ^ 2 * (2 * M) / Real.exp (3 * N) ^ 2)) * (2 ^ (P.d + 1) * P.L ^ (P.d + 1) * latConst P.d) := by
        gcongr; linarith
    _ = 8 * (2 ^ (P.d + 1) * latConst P.d) * (P.L ^ (P.d + 3) * M) / Real.exp (3 * N) ^ 2 := by ring
    _ ≤ Real.exp (-(4 * N)) / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num), hX6]
        have hA : 16 * (2 ^ (P.d + 1) * latConst P.d) * (P.L ^ (P.d + 3) * M) ≤ M * M := by
          have : 16 * (2 ^ (P.d + 1) * latConst P.d) * P.L ^ (P.d + 3) ≤ P.L ^ (P.d + 3) * P.L := by
            nlinarith [pow_nonneg hL0 (P.d + 3)]
          nlinarith [pow_nonneg hL0 (P.d + 3)]
        have hE : Real.exp (-(4 * N)) * Real.exp (4 * N) = 1 := by rw [← Real.exp_add]; simp
        calc 8 * (2 ^ (P.d + 1) * latConst P.d) * (P.L ^ (P.d + 3) * M) * 2
            = 16 * (2 ^ (P.d + 1) * latConst P.d) * (P.L ^ (P.d + 3) * M) := by ring
          _ ≤ Real.exp (2 * N) := hA.trans h2N
          _ = Real.exp (-(4 * N)) * (Real.exp (2 * N) * Real.exp (4 * N)) := by
              rw [mul_comm (Real.exp (2 * N)), ← mul_assoc, hE, one_mul]

theorem triK_le (P : WTParams) (p : ℕ) (hd : 1 ≤ P.d) (hL : Real.exp (100 * P.d + 11) ≤ P.L)
    (hγ : P.γ < 1) (hδ0 : 0 < P.δ) (hδ1 : P.δ ≤ 1) {Λ : ℝ}
    (hL3 : 18 * 3 ^ (Λ + 1) * 4 ^ (P.d + 1) * latConst P.d ^ 2 ≤ P.L) :
    triK P.d P.L P.γ P.δ Λ ≤ Real.exp (4 * P.N (p + 1)) / 18 := by
  have hL1 : 1 ≤ P.L := le_trans (Real.one_le_exp (by positivity)) hL
  have hL0 : 0 ≤ P.L := by linarith
  set N : ℝ := (P.N (p + 1) : ℝ)
  set M : ℝ := P.L ^ (100 * P.d : ℝ)
  have hEN := exp_N_ge P hd hL (p + 1)
  have hE10 : 1 ≤ Real.exp 10 := Real.one_le_exp (by norm_num)
  have hMN : M ≤ Real.exp N := le_trans (le_mul_of_one_le_left (Real.rpow_nonneg hL0 _) hE10) hEN
  have hM1 : 1 ≤ M := Real.one_le_rpow hL1 (by positivity)
  have hS := latConst_nonneg P.d
  have hT := latSum_le' (d := P.d) hL1
  have hT0 : 0 ≤ latSum P.d P.L := tsum_nonneg fun _ => Real.rpow_nonneg (jbr_pos'' _).le _
  have h3 : 0 < (3 : ℝ) ^ (Λ + 1) := Real.rpow_pos_of_pos (by norm_num) _
  -- the coupling factor is at most one
  have hc : |P.δ / (2 * P.L ^ ((P.d : ℝ) - P.γ))| ≤ 1 := by
    have hLp : 1 ≤ P.L ^ ((P.d : ℝ) - P.γ) :=
      Real.one_le_rpow hL1 (by have := (Nat.one_le_cast (α := ℝ)).2 hd; linarith)
    rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
    linarith
  have hMd : P.L ^ (2 * P.d + 2) * P.L ≤ M := by
    rw [← pow_succ]
    exact rpow_ge_pow hL1 (by push_cast; nlinarith [(Nat.one_le_cast (α := ℝ)).2 hd])
  have h4N : M ≤ Real.exp (4 * N) := by
    refine hMN.trans (Real.exp_le_exp.2 ?_)
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith
  unfold triK
  calc |P.δ / (2 * P.L ^ ((P.d : ℝ) - P.γ))| * (3 ^ (Λ + 1) * latSum P.d P.L ^ 2)
      ≤ 1 * (3 ^ (Λ + 1) * (2 ^ (P.d + 1) * P.L ^ (P.d + 1) * latConst P.d) ^ 2) := by
        gcongr
    _ = 3 ^ (Λ + 1) * 4 ^ (P.d + 1) * latConst P.d ^ 2 * P.L ^ (2 * P.d + 2) := by
        rw [one_mul, show (4 : ℝ) ^ (P.d + 1) = (2 ^ (P.d + 1)) ^ 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]]
        ring
    _ ≤ M / 18 := by
        rw [le_div_iff₀ (by norm_num)]
        nlinarith [pow_nonneg hL0 (2 * P.d + 2)]
    _ ≤ Real.exp (4 * N) / 18 := by gcongr

end WaveTurbulence.Fixedpt
