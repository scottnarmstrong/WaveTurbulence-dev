/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GateTypes
public import WaveTurbulence.Foundations.XChain.GeometricInputBound
/-! The actual high-order garden tail in S4 retains its geometric smallness. -/
public section
namespace WaveTurbulence.Induct
open Finset Set

theorem finite_geometric_squared_tail_le_two {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 2)
    (M K : ℕ) : (∑ N ∈ range K, if M ≤ N then q ^ (2 * N) else 0) ≤ 2 * q ^ M := by
  have hterm (N : ℕ) : (if M ≤ N then q ^ (2 * N) else 0) ≤ q ^ M * q ^ N := by
    split_ifs with hN
    · rw [mul_comm 2, pow_mul, pow_two]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hq (hq'.trans (by norm_num)) hN) (pow_nonneg hq N)
    · exact mul_nonneg (pow_nonneg hq _) (pow_nonneg hq _)
  calc
    _ ≤ ∑ N ∈ range K, q ^ M * q ^ N := sum_le_sum (fun N _ => hterm N)
    _ = q ^ M * ∑ N ∈ range K, q ^ N := (mul_sum ..).symm
    _ ≤ q ^ M * 2 := mul_le_mul_of_nonneg_left (sum_geometric_le_two hq hq' K) (pow_nonneg hq _)
    _ = _ := mul_comm _ _

theorem layergarden_higher_order_tail_bound (P : WTParams) (hG : LayergardenBody P)
    (R : ℕ → Mom P.d → ℝ) (p : ℕ) (hp : p < P.D) (hR : RemainderBound P R p)
    (hL : 0 < P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2)
    (m : ℕ) (hm : 2 ≤ m) (hmR : m ≤ 10 * P.R (p + 1))
    (sig : Fin (2 * m) → ℤˣ) (hbal : IsBalancedSig sig)
    (Ncut M : ℕ) (hcut : Ncut ≤ P.N (p + 1) ^ 4)
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) (n : Fin (2 * m) → (Fin P.d → ℤ)) :
    ‖∑ N ∈ range (Ncut + 1), if M ≤ N then truncSum P (inputsF P R) (p + 1) N t sig n else 0‖ ≤
      (jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4)) *
        (2 * (P.δ ^ P.ν) ^ M) := by
  let C : ℝ := jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4)
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by
    unfold jbrProd
    exact prod_nonneg (fun j _ => (jbr_pos _).le)) _) (Real.rpow_nonneg hL.le _)
  have hterm (N : ℕ) (hN : N ∈ range (Ncut + 1)) :
      ‖if M ≤ N then truncSum P (inputsF P R) (p + 1) N t sig n else 0‖ ≤
        C * (if M ≤ N then (P.δ ^ P.ν) ^ (2 * N) else 0) := by
    split_ifs
    · have h := (hG p hp R hR t ht N (by
        have hn := mem_range.mp hN
        omega)).1 m hm hmR sig hbal n
      have he : P.δ ^ (2 * P.ν * N) = (P.δ ^ P.ν) ^ (2 * N) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
        congr 1
        push_cast
        ring
      rw [he] at h
      exact h
    · simp
  calc
    _ ≤ ∑ N ∈ range (Ncut + 1), C * (if M ≤ N then (P.δ ^ P.ν) ^ (2 * N) else 0) :=
      (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ = C * ∑ N ∈ range (Ncut + 1), if M ≤ N then (P.δ ^ P.ν) ^ (2 * N) else 0 := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (finite_geometric_squared_tail_le_two (Real.rpow_nonneg hδ.le _) hsmall M (Ncut + 1)) hC

end WaveTurbulence.Induct
