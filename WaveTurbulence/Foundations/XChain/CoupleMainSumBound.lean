/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CoupleOrderSumIdentity
public import WaveTurbulence.Foundations.XChain.SNormDecay
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Trunc
/-! The actual two-point main sum has two individual root weights, using the exact couple/Taylor decomposition. -/
public section
namespace WaveTurbulence.Induct
open Finset Set

theorem couple_main_real_momentum_bound (P : WTParams) (hG : LayergardenBody P) (hW : WkeTaylorBody P)
    (R : ℕ → Mom P.d → ℝ) (p : ℕ) (hp : p < P.D) (hR : RemainderBound P R p)
    (hd : 1 ≤ P.d) (hL : 0 < P.L) (hδ : 0 < P.δ) (hC : 0 ≤ P.C₂)
    (hsmall : P.δ ^ (2 * P.ν) ≤ 1 / 2)
    (hr : 0 ≤ P.C₁ * P.δ) (hr1 : P.C₁ * P.δ < 1)
    (Ncut : ℕ) (hcut : Ncut ≤ P.N (p + 1) ^ 4)
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) (B : ℝ)
    (hφ : ∀ k, |P.φ (P.δ * t) k| ≤ B * jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)))
    (k : Mom P.d) :
    ‖∑ N ∈ range (Ncut + 1), truncSumC P (inputsF P R) (p + 1) N t k‖ ≤
      (B + 2 * P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) +
        P.C₂ * (P.C₁ * P.δ) ^ (Ncut / 2 + 1) / (1 - P.C₁ * P.δ)) *
          jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) := by
  have hrem := SNorm_decay_bound
    (fun k => ∑ N ∈ range (Ncut + 1), coupleRemainder P R p N t k)
    (2 * P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5)) (by positivity)
    (coupleRemainder_sum_SNorm_bound P hG R p hp hR hd hL hδ hsmall Ncut hcut t ht) k
  have htail := SNormR_pointwise (wkeTaylorTail P p (Ncut / 2 + 1) t)
    (P.C₂ * (P.C₁ * P.δ) ^ (Ncut / 2 + 1) / (1 - P.C₁ * P.δ))
    (div_nonneg (mul_nonneg hC (pow_nonneg hr _)) (sub_pos.mpr hr1).le)
    (wkeTaylorTail_SNormR_bound P hW hd p hp hC hr hr1 (Ncut / 2 + 1) t ⟨ht.1.le, ht.2⟩) k
  rw [couple_order_sum_eq_remainders_add_phi_sub_tail P hW R p hp Ncut t ⟨ht.1.le, ht.2⟩ k]
  have hh : ‖(∑ N ∈ range (Ncut + 1), coupleRemainder P R p N t k) +
      (P.φ (P.δ * t) k : ℂ) - (wkeTaylorTail P p (Ncut / 2 + 1) t k : ℂ)‖ ≤
      ‖∑ N ∈ range (Ncut + 1), coupleRemainder P R p N t k‖ +
        |P.φ (P.δ * t) k| + |wkeTaylorTail P p (Ncut / 2 + 1) t k| := by
    have h1 := norm_add_le (∑ N ∈ range (Ncut + 1), coupleRemainder P R p N t k)
      (P.φ (P.δ * t) k : ℂ)
    have h2 := norm_sub_le ((∑ N ∈ range (Ncut + 1), coupleRemainder P R p N t k) +
      (P.φ (P.δ * t) k : ℂ)) (wkeTaylorTail P p (Ncut / 2 + 1) t k : ℂ)
    simp only [Complex.norm_real, Real.norm_eq_abs] at h1 h2
    linarith
  push_cast at hrem htail

  have hφk := hφ k
  nlinarith

theorem couple_main_lattice_sum_bound (P : WTParams) (hG : LayergardenBody P) (hW : WkeTaylorBody P)
    (R : ℕ → Mom P.d → ℝ) (p : ℕ) (hp : p < P.D) (hR : RemainderBound P R p)
    (hd : 1 ≤ P.d) (hL : 0 < P.L) (hδ : 0 < P.δ) (hC : 0 ≤ P.C₂)
    (hsmall : P.δ ^ (2 * P.ν) ≤ 1 / 2)
    (hr : 0 ≤ P.C₁ * P.δ) (hr1 : P.C₁ * P.δ < 1)
    (Ncut : ℕ) (hcut : Ncut ≤ P.N (p + 1) ^ 4)
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) (B : ℝ) (hB : 0 ≤ B)
    (hφ : ∀ k, |P.φ (P.δ * t) k| ≤ B * jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)))
    (hrest : 2 * P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) +
      P.C₂ * (P.C₁ * P.δ) ^ (Ncut / 2 + 1) / (1 - P.C₁ * P.δ) ≤ 1)
    (n : Fin 2 → (Fin P.d → ℤ)) :
    ‖∑ N ∈ range (Ncut + 1), truncSum P (inputsF P R) (p + 1) N t ![1, -1] n‖ ≤
      (B + 1) * (∏ j, jbr (latticePoint P.L (n j))) ^ (-(2 * P.Lambda (p + 1) : ℝ)) := by
  classical
  by_cases hn : n 0 = n 1
  · have hnfun : n = fun _ => n 0 := by
      funext j
      fin_cases j
      · rfl
      · exact hn.symm
    have he := jbrProd_pair_rpow_half P.L n hn (4 * P.Lambda (p + 1) : ℝ)
    have hweight : (∏ j, jbr (latticePoint P.L (n j))) ^ (-(2 * P.Lambda (p + 1) : ℝ)) =
        jbr (latticePoint P.L (n 0)) ^ (-(4 * P.Lambda (p + 1) : ℝ)) := by
      convert he using 1 <;> congr 1 <;> ring
    rw [hweight, hnfun]
    simp_rw [Canon.truncSum_couple_eq_truncSumC]
    have h := couple_main_real_momentum_bound P hG hW R p hp hR hd hL hδ hC hsmall hr hr1
      Ncut hcut t ht B hφ (latticePoint P.L (n 0))
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (jbr_pos _).le _))
  · have hz (N : ℕ) (hN : N ∈ range (Ncut + 1)) : truncSum P (inputsF P R) (p + 1) N t ![1, -1] n = 0 :=
      (hG p hp R hR t ht N (by
        have h := mem_range.mp hN
        omega)).2.1 n hn
    simp only [sum_eq_zero hz, norm_zero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (zero_le_one.trans (one_le_jbrProd P.L n)) _)

end WaveTurbulence.Induct
