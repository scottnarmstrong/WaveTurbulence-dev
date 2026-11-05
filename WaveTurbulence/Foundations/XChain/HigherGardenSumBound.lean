/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.HigherGardenTail
/-! The actual finite proper-garden main term is uniformly bounded by its source spatial weight. -/
public section
namespace WaveTurbulence.Induct
open Finset Set

theorem layergarden_higher_sum_bound (P : WTParams) (hG : LayergardenBody P)
    (R : ℕ → Mom P.d → ℝ) (p : ℕ) (hp : p < P.D) (hR : RemainderBound P R p)
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2)
    (m : ℕ) (hm : 2 ≤ m) (hmR : m ≤ 10 * P.R (p + 1))
    (sig : Fin (2 * m) → ℤˣ) (hbal : IsBalancedSig sig)
    (Ncut : ℕ) (hcut : Ncut ≤ P.N (p + 1) ^ 4)
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) (n : Fin (2 * m) → (Fin P.d → ℤ)) :
    ‖∑ N ∈ range (Ncut + 1), truncSum P (inputsF P R) (p + 1) N t sig n‖ ≤
      2 * jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) := by
  have h := layergarden_higher_order_tail_bound P hG R p hp hR (zero_lt_one.trans_le hL)
    hδ hsmall m hm hmR sig hbal Ncut 0 hcut t ht n
  simp only [Nat.zero_le, ite_true, pow_zero, mul_one] at h
  have hscale : P.L ^ (-((m : ℝ) - 1) / 4) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by
      have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith)
  have hW : 0 ≤ jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) :=
    Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _
  have hs := mul_le_mul_of_nonneg_left hscale hW
  exact h.trans (by nlinarith)

end WaveTurbulence.Induct
