/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzInputKernelBound
public import WaveTurbulence.Foundations.XChain.LowerOrderProperSum
public import WaveTurbulence.Foundations.XChain.LowerOrderPairSum
/-! Exact-order input kernel bounds come directly from the actual order-by-order ansatz. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem ansatz_input_order_kernel_bound (P : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : (Fin P.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ)
    (p : ℕ) (N : Fin (P.N p + 1)) (ha : AnsatzAt P μ g a Fev R E Et p)
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF P R p (latticePoint P.L n)| ≤
      C * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)))
    {w : ℕ} (hw : 1 ≤ w) (hR : w ≤ 2 * P.R p) (sig : Fin w → ℤˣ)
    (n : Fin w → (Fin P.d → ℤ)) :
    ‖lowerOrderKernelSum P.L P.γ P.δ (inputsF P R) sig p (P.N p) N n‖ ≤
      C * (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ) / 2) * P.δ ^ (P.ν * N.1) := by
  classical
  by_cases hbal : ∑ j, (sig j : ℤ) = 0
  · have heven : Even w := by
      simpa only [card_univ, Fintype.card_fin] using even_card_of_balanced_units sig univ hbal
    obtain ⟨m, hm⟩ := heven
    have he : w = 2 * m := by omega
    clear hm
    subst w
    by_cases hm1 : m = 1
    · subst m
      rw [lowerOrderKernelSum_pair P.L P.γ P.δ (inputsF P R) sig N n]
      split_ifs with hN
      · have hb := lowerKernelSum_pair_bound P.L P.γ P.δ (inputsF P R) sig hbal p (P.N p)
          C (P.Lambda p) (by linarith) hF n
        simpa only [hN, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] using hb
      · rw [norm_zero]
        exact mul_nonneg (mul_nonneg (by linarith)
          (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _)) (Real.rpow_nonneg hδ.le _)

    · have hm2 : 2 ≤ m := by omega
      rw [lowerOrderKernelSum_eq_truncSum P (inputsF P R) sig p N (by omega) n]
      have hs := ha.2.2.2.2 m hm2 (by omega) sig hbal n N.1 (Nat.le_of_lt_succ N.2)
      have hscale : P.L ^ (-((m : ℝ) - 1) / 6) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hL (by
          have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
          linarith)
      have hW : (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ)) ≤
          (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_jbrProd P.L n) (by
          have hΛ : (0 : ℝ) ≤ P.Lambda p := Nat.cast_nonneg _
          linarith)
      have hn : 0 ≤ (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ) / 2) :=
        Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _
      have hbase : (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ)) *
          P.L ^ (-((m : ℝ) - 1) / 6) ≤
          C * (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ) / 2) := by
        have h := mul_le_mul hW hscale (Real.rpow_nonneg (zero_le_one.trans hL) _) hn
        nlinarith
      exact hs.trans (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hδ.le _))
  · rw [lowerOrderKernelSum_unbalanced P.L P.γ P.δ (inputsF P R) sig N hbal n, norm_zero]
    exact mul_nonneg (mul_nonneg (by linarith)
      (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _)) (Real.rpow_nonneg hδ.le _)

end WaveTurbulence.Induct
