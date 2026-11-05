/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GeometricInputBound
public import WaveTurbulence.Foundations.XChain.LowerPairKernelSum
public import WaveTurbulence.Foundations.XChain.SignatureParity
/-! Uniform main input-kernel bound from order sums and the actual two-point input. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem lowerKernelSum_pair_bound {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin 2 → ℤˣ) (hs : ∑ j, (sig j : ℤ) = 0) (p N : ℕ)
    (C Λ : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n : Fin d → ℤ, |F p (latticePoint L n)| ≤ C * jbr (latticePoint L n) ^ (-Λ))
    (n : Fin 2 → (Fin d → ℤ)) :
    ‖lowerKernelSum L γ δ F sig p N n‖ ≤ C * (∏ j, jbr (latticePoint L (n j))) ^ (-Λ / 2) := by
  rw [lowerKernelSum_pair L γ δ F sig (neg_sig_one_of_balanced_two sig hs) p N n]
  split_ifs with hn
  · rw [Complex.norm_real, Real.norm_eq_abs, jbrProd_pair_rpow_half L n hn]
    exact hF _
  · rw [norm_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd L n)) _)

theorem ansatz_input_kernel_bound (P : WTParams) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : (Fin P.d → ℤ) → Ω → ℂ)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ)
    (p : ℕ) (ha : AnsatzAt P μ g a Fev R E Et p)
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2)
    (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF P R p (latticePoint P.L n)| ≤
      C * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)))
    {w : ℕ} (hw : 1 ≤ w) (hR : w ≤ 2 * P.R p) (sig : Fin w → ℤˣ)
    (n : Fin w → (Fin P.d → ℤ)) :
    ‖lowerKernelSum P.L P.γ P.δ (inputsF P R) sig p (P.N p) n‖ ≤
      C * (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ) / 2) := by
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
      exact lowerKernelSum_pair_bound P.L P.γ P.δ (inputsF P R) sig hbal p (P.N p)
        C (P.Lambda p) (by linarith) hF n
    · have hm2 : 2 ≤ m := by omega
      exact (ansatz_higher_kernel_bound P μ g a Fev R E Et p ha hL hδ hsmall m hm2
        (by omega) sig hbal n).trans (mul_le_mul_of_nonneg_right hC
          (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _))
  · rw [lowerKernelSum_unbalanced P.L P.γ P.δ (inputsF P R) sig p (P.N p) hbal n, norm_zero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _)

end WaveTurbulence.Induct
