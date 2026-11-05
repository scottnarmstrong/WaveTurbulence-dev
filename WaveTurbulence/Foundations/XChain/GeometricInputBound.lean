/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzHigherResidual
public import WaveTurbulence.Foundations.XChain.JbrBounds
/-! Summing the actual order bounds retains a uniform constant in the lower garden kernel. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem sum_geometric_le_two {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1 / 2) (N : ℕ) :
    ∑ k ∈ range N, r ^ k ≤ 2 := by
  have h : ∀ n, (∑ k ∈ range n, r ^ k) + 2 * r ^ n ≤ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, pow_succ]
      have hp := pow_nonneg hr n
      nlinarith
  exact (le_add_of_nonneg_right (mul_nonneg (by norm_num) (pow_nonneg hr N))).trans (h N)

theorem ansatz_higher_kernel_bound (P : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : (Fin P.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt P μ g a Fev R E Et p)
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2)
    (m : ℕ) (hm : 2 ≤ m) (hR : m ≤ P.R p) (sig : Fin (2 * m) → ℤˣ)
    (hbal : ∑ j, (sig j : ℤ) = 0) (n : Fin (2 * m) → (Fin P.d → ℤ)) :
    ‖lowerKernelSum P.L P.γ P.δ (inputsF P R) sig p (P.N p) n‖ ≤
      2 * (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ) / 2) := by
  classical
  let W := (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ))
  have hW : 0 ≤ W := Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _
  have hscale : P.L ^ (-((m : ℝ) - 1) / 6) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by
      have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith)
  have horder (N : ℕ) (hN : N ∈ range (P.N p + 1)) :
      ‖truncSum P (inputsF P R) p N p sig n‖ ≤ W * (P.δ ^ P.ν) ^ N := by
    have h := ha.2.2.2.2 m hm hR sig hbal n N (Nat.le_of_lt_succ (mem_range.mp hN))
    have he : P.δ ^ (P.ν * N) = (P.δ ^ P.ν) ^ N := by
      rw [Real.rpow_mul hδ.le, Real.rpow_natCast]
    rw [he] at h
    have hs : W * P.L ^ (-((m : ℝ) - 1) / 6) ≤ W := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale hW
    exact h.trans (mul_le_mul_of_nonneg_right hs (pow_nonneg (Real.rpow_nonneg hδ.le _) _))
  rw [lowerKernelSum_eq_sum_truncSum P (inputsF P R) sig p (by omega) n]
  calc
    ‖∑ N ∈ range (P.N p + 1), truncSum P (inputsF P R) p N p sig n‖ ≤
        ∑ N ∈ range (P.N p + 1), W * (P.δ ^ P.ν) ^ N :=
      (norm_sum_le _ _).trans (sum_le_sum horder)
    _ = W * ∑ N ∈ range (P.N p + 1), (P.δ ^ P.ν) ^ N := (mul_sum ..).symm
    _ ≤ W * 2 := mul_le_mul_of_nonneg_left
      (sum_geometric_le_two (Real.rpow_nonneg hδ.le _) hsmall _) hW
    _ ≤ 2 * (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ) / 2) := by
      rw [mul_comm W]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
        (one_le_jbrProd P.L n) (by
          have hΛ : (0 : ℝ) ≤ P.Lambda p := Nat.cast_nonneg _
          linarith)) (by norm_num)

end WaveTurbulence.Induct
