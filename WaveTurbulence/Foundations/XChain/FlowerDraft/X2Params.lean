/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-!
# Parameter facts used by X2 and X3

* `N_ge_log`: for `L ≥ e^{100d+11}` and `q ≤ 𝔇`, `N_q ≥ 100 d log L + 10`. Every `e^{−N_q}` therefore beats
  `L^{−100d}`, which is how the losses `L^{C}` of `flowerest1`/`fixedpoint` are absorbed. The proof uses
  `N_q = R_q^{40d} ≥ R_q ≥ R_𝔇 = ⌊(log L)^{40d}⌋`.
* `norm_le_of_SNorm_le`: an `𝔖^{Λ₁,Λ₂}` bound gives the pointwise bound `⟨k⟩^{Λ₂} |F(k)| ≤ M` (the `ρ = 0` term).
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

namespace WTParams

variable (P : WTParams)

theorem one_le_Rdown_zero (hx : 1 ≤ Real.log P.L) : 1 ≤ P.Rdown 0 := by
  show 1 ≤ ⌊Real.log P.L ^ (40 * P.d)⌋₊
  exact Nat.one_le_floor_iff _ |>.2 (one_le_pow₀ hx)

theorem Rdown_zero_le (hd : 1 ≤ P.d) (h1 : 1 ≤ P.Rdown 0) : ∀ k, P.Rdown 0 ≤ P.Rdown k
  | 0 => le_rfl
  | k + 1 => by
    have ih := Rdown_zero_le hd h1 k
    have hn : 40 * P.d ≠ 0 := by omega
    show P.Rdown 0 ≤ (P.Rdown k ^ (40 * P.d)) ^ (40 * P.d)
    exact ih.trans ((Nat.le_self_pow hn _).trans (Nat.le_self_pow hn _))

theorem Rdown_zero_le_N (hd : 1 ≤ P.d) (h1 : 1 ≤ P.Rdown 0) (q : ℕ) : P.Rdown 0 ≤ P.N q := by
  unfold WTParams.N WTParams.R
  have h := Rdown_zero_le P hd h1 (P.D - q)
  have hpos : 1 ≤ P.Rdown (P.D - q) := h1.trans h
  exact h.trans (Nat.le_self_pow (by omega) _)

/-- **`N_q` beats `log L`.** -/
theorem N_ge_log (hd : 1 ≤ P.d) (hL : Real.exp (100 * P.d + 11) ≤ P.L) (q : ℕ) :
    100 * P.d * Real.log P.L + 10 ≤ P.N q := by
  have hLpos : 0 < P.L := (Real.exp_pos _).trans_le hL
  set x := Real.log P.L with hx
  have hx0 : 100 * (P.d : ℝ) + 11 ≤ x := by
    rw [hx, ← Real.exp_le_exp, Real.exp_log hLpos]
    exact hL
  have hx1 : 1 ≤ x := le_trans (by have : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _; linarith) hx0
  have h1 : 1 ≤ P.Rdown 0 := one_le_Rdown_zero P hx1
  have hN : (P.Rdown 0 : ℝ) ≤ P.N q := by exact_mod_cast Rdown_zero_le_N P hd h1 q
  have hfloor : x ^ (40 * P.d) - 1 ≤ (P.Rdown 0 : ℝ) := by
    show x ^ (40 * P.d) - 1 ≤ ((⌊Real.log P.L ^ (40 * P.d)⌋₊ : ℕ) : ℝ)
    have := Nat.lt_floor_add_one (Real.log P.L ^ (40 * P.d))
    linarith
  have hpow : x * (100 * P.d + 11) ≤ x ^ (40 * P.d) := by
    have hk : 40 * P.d = (40 * P.d - 1) + 1 := by omega
    rw [hk, pow_succ, mul_comm (x ^ (40 * P.d - 1)) x]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    calc 100 * (P.d : ℝ) + 11 ≤ x := hx0
      _ = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ (40 * P.d - 1) := pow_le_pow_right₀ hx1 (by omega)
  have : 100 * (P.d : ℝ) * x + 10 ≤ x ^ (40 * P.d) - 1 := by nlinarith
  linarith

end WTParams

namespace X2E

/-- **An `𝔖^{Λ₁,Λ₂}` bound gives a pointwise bound.** -/
theorem norm_le_of_SNorm_le {d : ℕ} {Λ₁ Λ₂ : ℕ} {F : Mom d → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (h : SNorm Λ₁ Λ₂ F ≤ ENNReal.ofReal M) (k : Mom d) : jbr k ^ Λ₂ * ‖F k‖ ≤ M := by
  unfold SNorm at h
  split_ifs at h with hg
  · have h0 : ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial (0 : Fin d → ℕ) F k‖) ≤ ENNReal.ofReal M :=
      le_trans (le_iSup₂_of_le (0 : Fin d → ℕ) (by simp)
        (le_iSup (fun k => ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial (0 : Fin d → ℕ) F k‖)) k)) h
    have hip : iterPartial (0 : Fin d → ℕ) F = F := by
      unfold iterPartial
      induction (List.finRange d) with
      | nil => rfl
      | cons j l _ => simp [List.foldr_cons]
    rw [hip, ENNReal.ofReal_le_ofReal_iff hM] at h0
    exact h0
  · exact absurd h (by simp)

theorem norm_le_of_SNormR_le {d : ℕ} {Λ₁ Λ₂ : ℕ} {F : Mom d → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : SNormR Λ₁ Λ₂ F ≤ ENNReal.ofReal M) (k : Mom d) : jbr k ^ Λ₂ * |F k| ≤ M := by
  have := norm_le_of_SNorm_le hM h k
  simpa [Complex.norm_real] using this

end X2E

end WaveTurbulence
