/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantDoubleton
public import WaveTurbulence.Foundations.XChain.SignedIntegrals
public import WaveTurbulence.Foundations.XChain.LowerPairKernelSum
/-! Either balanced two-point signature has the same diagonal covariance. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem integral_signed_pair_of_covariance {Ω α : Type*} [MeasurableSpace Ω] [DecidableEq α]
    (μ : Measure Ω) (X : Ω → α → ℂ) (W : α → ℝ)
    (hcov : ∀ n n', (∫ ω, X ω n * (starRingEnd ℂ) (X ω n') ∂μ) =
      if n = n' then (W n : ℂ) else 0)
    (sig : Fin 2 → ℤˣ) (hbal : ∑ j, (sig j : ℤ) = 0) (n : Fin 2 → α) :
    (∫ ω, zpowSign (sig 0) (X ω (n 0)) * zpowSign (sig 1) (X ω (n 1)) ∂μ) =
      if n 0 = n 1 then (W (n 0) : ℂ) else 0 := by
  have hs := neg_sig_one_of_balanced_two sig hbal
  rcases Int.units_eq_one_or (sig 0) with h0 | h0
  · have h1 : sig 1 = -1 := hs.trans (congrArg Neg.neg h0)
    have hf : (fun ω => zpowSign (sig 0) (X ω (n 0)) * zpowSign (sig 1) (X ω (n 1))) =
        fun ω => X ω (n 0) * (starRingEnd ℂ) (X ω (n 1)) := by
      funext ω
      simp [zpowSign, h0, h1]
    rw [hf, hcov]
  · have h1 : sig 1 = 1 := hs.trans (by rw [h0, neg_neg])
    have hf : (fun ω => zpowSign (sig 0) (X ω (n 0)) * zpowSign (sig 1) (X ω (n 1))) =
        fun ω => X ω (n 1) * (starRingEnd ℂ) (X ω (n 0)) := by
      funext ω
      simp [zpowSign, h0, h1, mul_comm]
    rw [hf, hcov]
    by_cases hn : n 0 = n 1
    · rw [ite_eq_left hn.symm, ite_eq_left hn]
      exact congrArg (fun a => (W a : ℂ)) hn.symm
    · rw [ite_eq_right (Ne.symm hn), ite_eq_right hn]

theorem cumulant_signed_pair_of_covariance {Ω α : Type*} [MeasurableSpace Ω] [DecidableEq α]
    (μ : Measure Ω) (X : Ω → α → ℂ) (W : α → ℝ)
    (hcov : ∀ n n', (∫ ω, X ω n * (starRingEnd ℂ) (X ω n') ∂μ) =
      if n = n' then (W n : ℂ) else 0)
    (hmean : ∀ n, (∫ ω, X ω n ∂μ) = 0)
    (sig : Fin 2 → ℤˣ) (hbal : ∑ j, (sig j : ℤ) = 0) (n : Fin 2 → α) :
    cumulant μ (fun j ω => zpowSign (sig j) (X ω (n j))) univ =
      if n 0 = n 1 then (W (n 0) : ℂ) else 0 := by
  have hm : (∫ ω, zpowSign (sig 0) (X ω (n 0)) ∂μ) = 0 := by
    rw [← zpowSign_integral, hmean]
    simp only [zpowSign, map_zero, ite_self]
  rw [cumulant_fin_two, hm, zero_mul, sub_zero]
  exact integral_signed_pair_of_covariance μ X W hcov sig hbal n

end WaveTurbulence.Induct
