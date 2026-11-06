/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Arith1
import Mathlib.Tactic
/-! The product of the per-ladder estimates. -/
@[expose] public section
open Finset
namespace WaveTurbulence.Ladder

theorem arith_total {Q : Type} [Fintype Q] [DecidableEq Q] (m K : Q → ℕ) (small : Q → Prop)
    (X ρ : Q → ℝ) (nfree n d : ℕ) {δ ν Dt Y Λ a dR Lam C1 : ℝ}
    (hn : n = nfree + ∑ S, (2 * m S + 2))
    (hK : ∀ S, K S ≤ m S) (hKs : ∀ S, small S → m S ≤ K S + d + 1) (hK0 : ∀ S, ¬ small S → K S = 0)
    (hX1 : ∀ S, small S → 1 ≤ X S) (hρ0 : ∀ S, 0 ≤ ρ S) (hρ : ∀ S, small S → ρ S ≤ 8 * a * X S)
    (hXL : ∀ S, ¬ small S → X S = Λ ^ 2)
    (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν) (hDt : 0 ≤ Dt)
    (hY1 : 1 ≤ Y) (hY : Y ≤ 180 * dR * Λ) (ha : 1 ≤ a) (hd : (d : ℝ) = dR) (hdR : 1 ≤ dR)
    (hexp : Real.exp (Dt * δ ^ (1 + 10 * ν) * Λ) * Λ ^ (2 * d + 4) ≤ Lam)
    (hΛLam : Λ ^ 2 ≤ Lam) (hfree : 128 * (180 * dR * Λ) ≤ Lam)
    (hC : 128 * (180 * dR) * (64 * a) ≤ C1) (hC1 : 1 ≤ C1) :
    (∏ S, (8 * ρ S * Dt) ^ (K S) / (Nat.factorial (K S) : ℝ)) * 128 ^ n * Y ^ (n - ∑ S, K S) ≤
      (C1 * δ ^ (-1 / 2 - 5 * ν)) ^ n * Lam ^ (Fintype.card Q + nfree) * ∏ S, X S ^ (m S) := by
  set Dl := δ ^ (-1 / 2 - 5 * ν) with hDl
  have hDl1 : 1 ≤ Dl := one_le_Dl hδ hδ1 hν
  have hLam1 : 1 ≤ Lam := by
    have : 1 ≤ Real.exp (Dt * δ ^ (1 + 10 * ν) * Λ) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ Λ ^ (2 * d + 4) := one_le_pow₀ hΛ
    nlinarith
  have hKN : ∀ S, K S ≤ 2 * m S + 2 := fun S => by have := hK S; omega
  have hsumK : ∑ S, K S ≤ ∑ S, (2 * m S + 2) := Finset.sum_le_sum (fun S _ => hKN S)
  have hmtot : n - ∑ S, K S = nfree + ∑ S, (2 * m S + 2 - K S) := by
    have : ∑ S, (2 * m S + 2 - K S) = ∑ S, (2 * m S + 2) - ∑ S, K S :=
      Finset.sum_tsub_distrib _ (fun S _ => hKN S)
    omega
  have hLHS : (∏ S, (8 * ρ S * Dt) ^ (K S) / (Nat.factorial (K S) : ℝ)) * 128 ^ n * Y ^ (n - ∑ S, K S) =
      (128 * Y) ^ nfree * ∏ S, (128 ^ (2 * m S + 2) * ((8 * ρ S * Dt) ^ (K S) / (Nat.factorial (K S) : ℝ)) *
        Y ^ (2 * m S + 2 - K S)) := by
    rw [hmtot, hn, pow_add, pow_add, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, mul_pow]
    ring
  have hRHS : (C1 * Dl) ^ n * Lam ^ (Fintype.card Q + nfree) * ∏ S, X S ^ (m S) =
      ((C1 * Dl) * Lam) ^ nfree * ∏ S, ((C1 * Dl) ^ (2 * m S + 2) * Lam * X S ^ (m S)) := by
    rw [hn, pow_add, pow_add, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, mul_pow]
    ring
  rw [hLHS, hRHS]
  have hC0 : 0 ≤ C1 := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hnn : ∀ S, 0 ≤ 128 ^ (2 * m S + 2) * ((8 * ρ S * Dt) ^ (K S) / (Nat.factorial (K S) : ℝ)) *
      Y ^ (2 * m S + 2 - K S) := fun S =>
    mul_nonneg (mul_nonneg (by positivity) (div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hρ0 S)) hDt) _)
      (by positivity))) (pow_nonneg hY0 _)
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg (fun S _ => hnn S)) (by positivity)
  · apply pow_le_pow_left₀ (by positivity)
    calc 128 * Y ≤ 128 * (180 * dR * Λ) := by gcongr
      _ ≤ Lam := hfree
      _ = 1 * Lam := by ring
      _ ≤ (C1 * Dl) * Lam := by
          gcongr
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ C1 * Dl := by gcongr
  · refine Finset.prod_le_prod₀ (fun S _ => hnn S) (fun S _ => ?_)
    by_cases hs : small S
    · exact small_factor (c1 := 128) (c2 := 180) (c3 := 64) (e := 8) (f := 8) (hX1 S hs) hΛ hδ hδ1 hν hDt (hρ0 S) (hρ S hs) hY1 hY ha hd hdR (hKs S hs) (hK S)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hexp
        (by simpa using hC)
    · rw [hK0 S hs, hXL S hs]
      simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, mul_one, Nat.sub_zero]
      exact large_factor (c1 := 128) (c2 := 180) hΛ hδ hδ1 hν hY1 hY hdR (by norm_num) (by norm_num) hΛLam
        ((le_mul_of_one_le_right (by positivity) (by linarith)).trans hC)

end WaveTurbulence.Ladder
