/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.HigherGardenTail
/-! The finite higher-garden order tail is exponentially small at the next ansatz cutoff. -/
public section
namespace WaveTurbulence.Induct
open Finset Set

theorem twice_geometric_tail_le_exp {r : ℝ} (hr : 0 ≤ r) (hre : r ≤ Real.exp (-21)) (N : ℕ) :
    2 * r ^ (N + 1) ≤ Real.exp (-(20 * (N : ℝ))) := by
  have hpow := pow_le_pow_left₀ hr hre (N + 1)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h := mul_le_mul htwo hpow (pow_nonneg hr _) (Real.exp_pos (1 : ℝ)).le
  rw [← Real.exp_nat_mul, ← Real.exp_add] at h
  exact h.trans (Real.exp_le_exp.mpr (by push_cast; nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]))

theorem layergarden_higher_tail_exp_bound (P : WTParams) (hG : LayergardenBody P)
    (R : ℕ → Mom P.d → ℝ) (p : ℕ) (hp : p < P.D) (hR : RemainderBound P R p)
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2)
    (hre : P.δ ^ P.ν ≤ Real.exp (-21))
    (m : ℕ) (hm : 2 ≤ m) (hmR : m ≤ 10 * P.R (p + 1))
    (sig : Fin (2 * m) → ℤˣ) (hbal : IsBalancedSig sig)
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) (n : Fin (2 * m) → (Fin P.d → ℤ)) :
    ‖∑ N ∈ range (P.N (p + 1) ^ 4 + 1), if P.N (p + 1) + 1 ≤ N then
        truncSum P (inputsF P R) (p + 1) N t sig n else 0‖ ≤
      jbrProd P.L n ^ (-(P.Lambda (p + 1) : ℝ)) * Real.exp (-(20 * (P.N (p + 1) : ℝ))) := by
  have h := layergarden_higher_order_tail_bound P hG R p hp hR (zero_lt_one.trans_le hL)
    hδ hsmall m hm hmR sig hbal (P.N (p + 1) ^ 4) (P.N (p + 1) + 1) le_rfl t ht n
  have hweight : jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) *
      P.L ^ (-((m : ℝ) - 1) / 4) ≤ jbrProd P.L n ^ (-(P.Lambda (p + 1) : ℝ)) := by
    have hs := Real.rpow_le_one_of_one_le_of_nonpos hL (show -((m : ℝ) - 1) / 4 ≤ 0 by
      have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith)
    have hw := Real.rpow_le_rpow_of_exponent_le (one_le_jbrProd P.L n)
      (show -(4 * P.Lambda (p + 1) : ℝ) ≤ -(P.Lambda (p + 1) : ℝ) by
        have hΛ : (0 : ℝ) ≤ P.Lambda (p + 1) := Nat.cast_nonneg _
        linarith)
    simpa only [mul_one, jbrProd] using mul_le_mul hw hs (Real.rpow_nonneg (zero_le_one.trans hL) _) (by
      exact Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _)
  exact h.trans (mul_le_mul hweight (twice_geometric_tail_le_exp (Real.rpow_nonneg hδ.le _) hre _)
    (mul_nonneg (by norm_num) (pow_nonneg (Real.rpow_nonneg hδ.le _) _))
    (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _))

end WaveTurbulence.Induct
