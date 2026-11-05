/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantDoubleton
public import WaveTurbulence.Foundations.XChain.LowerPairKernelSum
/-! Either balanced two-point sign orientation is exactly the canonical covariance with reordered labels. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem balanced_pair_sign_cases (sig : Fin 2 → ℤˣ) (hs : ∑ j, (sig j : ℤ) = 0) :
    sig = ![1, -1] ∨ sig = ![-1, 1] := by
  have h1 := neg_sig_one_of_balanced_two sig hs
  rcases Int.units_eq_one_or (sig 0) with h0 | h0
  · left
    funext j
    fin_cases j
    · exact h0
    · change sig 1 = -1
      simpa only [h0] using h1
  · right
    funext j
    fin_cases j
    · exact h0
    · change sig 1 = 1
      simpa only [h0, neg_neg] using h1

theorem cumulant_fin_two_reverse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Fin 2 → Ω → ℂ) : cumulant μ (fun j : Fin 2 => X j.rev) univ = cumulant μ X univ := by
  rw [cumulant_fin_two, cumulant_fin_two]
  change (∫ ω, X 1 ω * X 0 ω ∂μ) - (∫ ω, X 1 ω ∂μ) * ∫ ω, X 0 ω ∂μ =
    (∫ ω, X 0 ω * X 1 ω ∂μ) - (∫ ω, X 0 ω ∂μ) * ∫ ω, X 1 ω ∂μ
  have he : (fun ω => X 1 ω * X 0 ω) = fun ω => X 0 ω * X 1 ω := by
    funext ω
    exact mul_comm _ _
  rw [he, mul_comm (∫ ω, X 1 ω ∂μ) (∫ ω, X 0 ω ∂μ)]

theorem cumulant_signed_pair_reverse {Ω β : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → β → ℂ) (n : Fin 2 → β) :
    cumulant μ (fun (j : Fin 2) ω => zpowSign (![-1, 1] j) (Z ω (n j))) univ =
      cumulant μ (fun (j : Fin 2) ω => zpowSign (![1, -1] j) (Z ω (n j.rev))) univ := by
  have he := cumulant_fin_two_reverse μ
    (fun (j : Fin 2) ω => zpowSign (![-1, 1] j) (Z ω (n j)))
  have hfun : (fun (j : Fin 2) ω => zpowSign (![-1, 1] j.rev) (Z ω (n j.rev))) =
      fun (j : Fin 2) ω => zpowSign (![1, -1] j) (Z ω (n j.rev)) := by
    funext j ω
    fin_cases j <;> rfl
  exact he.symm.trans (congrArg (fun X : Fin 2 → Ω → ℂ => cumulant μ X univ) hfun)

end WaveTurbulence.Induct
