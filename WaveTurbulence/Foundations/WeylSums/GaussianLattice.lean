/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds

/-!
# Uniform Gaussian lattice tails

Poisson summation after rational completion produces a shifted Gaussian
lattice sum. A fixed positive lower bound on its decay coefficient makes
the entire tail uniformly bounded, independently of the shift.
-/

public section

open scoped BigOperators
open HurwitzKernelBounds

namespace WaveTurbulence.WeylSums

/-- Summability of a shifted Gaussian on the integer lattice. -/
theorem summable_gaussian_lattice (u : ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * ((n : ℝ) - u) ^ 2 * t)) := by
  apply (summable_f_int 0 (-u) ht).congr
  intro n
  simp only [f_int, pow_zero, one_mul, sub_eq_add_neg]

/-- Uniform Gaussian lattice bound, using a geometric majorant for each half
of the lattice after shifting the center into one fundamental interval. -/
theorem tsum_gaussian_lattice_le (u : ℝ) {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    (∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) - u) ^ 2 * t)) ≤
      2 / (1 - Real.exp (-Real.pi * t₀)) := by
  have htpos : 0 < t := ht₀.trans_le ht
  have hden₀ : 0 < 1 - Real.exp (-Real.pi * t₀) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    simpa only [neg_mul] using neg_neg_of_pos (mul_pos Real.pi_pos ht₀)
  have hden : 0 < 1 - Real.exp (-Real.pi * t) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    simpa only [neg_mul] using neg_neg_of_pos (mul_pos Real.pi_pos htpos)
  have hdenle : 1 - Real.exp (-Real.pi * t₀) ≤ 1 - Real.exp (-Real.pi * t) := by
    apply sub_le_sub_left
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left ht (neg_nonpos.mpr Real.pi_pos.le)
  have hhalf (a : ℝ) (ha : 0 ≤ a) : F_nat 0 a t ≤ 1 / (1 - Real.exp (-Real.pi * t₀)) := by
    calc
      _ ≤ ‖F_nat 0 a t‖ := le_abs_self _
      _ ≤ Real.exp (-Real.pi * a ^ 2 * t) / (1 - Real.exp (-Real.pi * t)) :=
        F_nat_zero_le ha htpos
      _ ≤ 1 / (1 - Real.exp (-Real.pi * t)) := by
        apply div_le_div_of_nonneg_right _ hden.le
        apply Real.exp_le_one_iff.mpr
        have h : 0 ≤ Real.pi * a ^ 2 * t := mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) htpos.le
        nlinarith only [h]
      _ ≤ _ := one_div_le_one_div_of_le hden₀ hdenle
  let a : ℝ := Int.fract (-u)
  have ha : a ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have heq : (∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) - u) ^ 2 * t)) =
      F_int 0 ((-u : ℝ) : UnitAddCircle) t := by
    simp only [F_int, Function.Periodic.lift_coe, f_int, pow_zero, one_mul, sub_eq_add_neg]
  have hproj : ((-u : ℝ) : UnitAddCircle) = (a : UnitAddCircle) := (AddCircle.coe_fract (-u)).symm
  rw [heq, hproj, F_int_eq_of_mem_Icc 0 ha htpos]
  have h₁ := hhalf a ha.1
  have h₂ := hhalf (1 - a) (sub_nonneg.mpr ha.2)
  rw [show (2 : ℝ) / (1 - Real.exp (-Real.pi * t₀)) =
    1 / (1 - Real.exp (-Real.pi * t₀)) + 1 / (1 - Real.exp (-Real.pi * t₀)) by ring]
  exact add_le_add h₁ h₂

end WaveTurbulence.WeylSums
