/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GateTypes
public import WaveTurbulence.Foundations.XChain.JbrBounds
/-! The stronger layergarden estimate implies the literal next-stage order-N ansatz bound. -/
public section
namespace WaveTurbulence.Induct
open Set

theorem layergarden_next_order_bound (P : WTParams) (hG : LayergardenBody P)
    (R : ℕ → Mom P.d → ℝ) (p : ℕ) (hp : p < P.D) (hR : RemainderBound P R p)
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hδ1 : P.δ ≤ 1) (hν : 0 ≤ P.ν)
    (hN : 1 ≤ P.N (p + 1)) (m : ℕ) (hm : 2 ≤ m) (hmR : m ≤ P.R (p + 1))
    (sig : Fin (2 * m) → ℤˣ) (hbal : IsBalancedSig sig)
    (n : Fin (2 * m) → (Fin P.d → ℤ)) (N : ℕ) (hNN : N ≤ P.N (p + 1))
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) :
    ‖truncSum P (inputsF P R) (p + 1) N t sig n‖ ≤
      (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda (p + 1) : ℝ)) *
        P.L ^ (-((m : ℝ) - 1) / 6) * P.δ ^ (P.ν * N) := by
  have hcut : N ≤ P.N (p + 1) ^ 4 :=
    hNN.trans (le_self_pow₀ hN (by omega))
  have h := (hG p hp R hR t ht N hcut).1 m hm (by omega) sig hbal n
  have hw : jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) ≤
      (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda (p + 1) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (one_le_jbrProd P.L n)
    have hΛ : (0 : ℝ) ≤ P.Lambda (p + 1) := Nat.cast_nonneg _
    linarith
  have hl : P.L ^ (-((m : ℝ) - 1) / 4) ≤ P.L ^ (-((m : ℝ) - 1) / 6) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hdd : P.δ ^ (2 * P.ν * N) ≤ P.δ ^ (P.ν * N) := by
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith [mul_nonneg hν hN0]
  exact h.trans (mul_le_mul (mul_le_mul hw hl (Real.rpow_nonneg (zero_le_one.trans hL) _)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _)) hdd
    (Real.rpow_nonneg hδ.le _) (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _)
      (Real.rpow_nonneg (zero_le_one.trans hL) _)))

end WaveTurbulence.Induct
