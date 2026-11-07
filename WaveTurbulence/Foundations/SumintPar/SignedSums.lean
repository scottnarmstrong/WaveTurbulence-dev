/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.Data
import Mathlib.Tactic

/-!
# Signed-sum bounds for the alternative-variable localization

The exact source coefficients lie in `{0,±1}`. Their total absolute mass
is therefore precisely the number of nonzero terms counted by Λ.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- Absolute coefficient mass equals the exact nonzero-term count in hypothesis (ii). -/
theorem sum_abs_unitCoeff_eq_count {ι : Type*} [Fintype ι] (σ : ι → ℤ)
    (hσ : ∀ i, IsUnitCoeff (σ i)) :
    (∑ i, |(σ i : ℝ)|) = ((Finset.univ.filter (fun i => σ i ≠ 0)).card : ℝ) := by
  classical
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rcases hσ i with h | h | h <;> simp [h]

/-- A real signed sum is bounded by the coefficient mass times a common magnitude bound. -/
theorem abs_sum_mul_le {ι : Type*} [Fintype ι] (σ y : ι → ℝ) {R : ℝ}
    (hy : ∀ i, |y i| ≤ R) : |∑ i, σ i * y i| ≤ (∑ i, |σ i|) * R := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i, |σ i| * R := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hy i) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- A finite scalar identity used when comparing actual variables with their cube centers. -/
theorem sum_mul_difference {ι : Type*} [Fintype ι] (σ y z : ι → ℝ) (c : ℝ) :
    (∑ i, σ i * (c * y i - z i)) = c * ∑ i, σ i * y i - ∑ i, σ i * z i := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The draft Λ bound controls the combined k/output coefficient mass. -/
theorem coefficient_mass_le {d : ℕ} (D : SumintDatum d) {A L γ η : ℝ} {Dsteps : ℕ}
    (hD : D.Admissible A L γ η Dsteps) (v : D.S.VIdx) :
    (∑ w, |(D.σk v w : ℝ)|) + ∑ c, |(D.σe v c : ℝ)| ≤ (D.Λ v : ℝ) := by
  obtain ⟨hk, he, hc, _, _, _⟩ := hD.1 v
  rw [sum_abs_unitCoeff_eq_count _ hk, sum_abs_unitCoeff_eq_count _ he]
  exact_mod_cast hc

end WaveTurbulence.SumintPar
