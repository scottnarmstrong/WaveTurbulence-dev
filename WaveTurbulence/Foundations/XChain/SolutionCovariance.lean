/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.AnsatzMeans
public import WaveTurbulence.Foundations.XChain.MomentumSupport
public import WaveTurbulence.Foundations.XChain.CumulantDoubleton
/-! Actual classed solutions on symmetric rapid-data events have zero means and diagonal covariance. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

section
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {L γ δ T : ℝ} (hL : 0 < L) (φ : Mom d → ℝ)
    {g : (Fin d → ℤ) → Ω → ℂ} (hG : IsGaussianData μ g)
    (F : Set Ω) (hFm : MeasurableSet F) (hF : IsSymmetricEvent L φ g F)
    (a : Ω → ℝ → (Fin d → ℤ) → ℂ)
    (ha : ∀ ω ∈ F, IsASolution L γ δ T (initialCoeff L φ g ω) (a ω))
    (hrapid : ∀ ω ∈ F, IsRapidDecay (initialCoeff L φ g ω))
    (hmeas : ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω => a ω t n)
    (t : ℝ) (ht : t ∈ Icc 0 T)
include hL hG hFm hF ha hrapid hmeas ht

theorem solution_mean_zero (n : Fin d → ℤ) : (∫ ω in F, a ω t n ∂μ) = 0 := by
  have hz := cumulant_signed_solution_eq_zero_of_unbalanced (ι := Fin 1) hL φ hG F hFm hF
    a ha hrapid hmeas (fun _ => ⟨t, ht⟩) (fun _ => n) (fun _ => (1 : ℤˣ)) {0} (by simp)
  simpa only [cumulant_singleton, zpowSign, ite_true] using hz

theorem solution_pair_cumulant_eq_integral (n : Fin 2 → (Fin d → ℤ)) :
    cumulant (μ.restrict F) (fun j ω => zpowSign (![1, -1] j) (a ω t (n j))) univ =
      ∫ ω in F, a ω t (n 0) * (starRingEnd ℂ) (a ω t (n 1)) ∂μ := by
  rw [cumulant_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    zpowSign, ite_true, show (-1 : ℤˣ) ≠ 1 from by decide, ite_false]
  rw [solution_mean_zero hL φ hG F hFm hF a ha hrapid hmeas t ht, zero_mul, sub_zero]

theorem solution_covariance_off_diagonal (n n' : Fin d → ℤ) (hn : n ≠ n') :
    (∫ ω in F, a ω t n * (starRingEnd ℂ) (a ω t n') ∂μ) = 0 := by
  have hz := cumulant_signed_solution_eq_zero_of_momentum hL φ hG F hFm hF a ha hrapid hmeas
    (fun _ : Fin 2 => ⟨t, ht⟩) ![n, n'] ![1, -1] univ (by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Units.val_one, Units.val_neg, one_smul, neg_smul,
        ← sub_eq_add_neg, sub_ne_zero] using hn)
  rw [solution_pair_cumulant_eq_integral hL φ hG F hFm hF a ha hrapid hmeas t ht] at hz
  simpa using hz

end
end WaveTurbulence.Induct
