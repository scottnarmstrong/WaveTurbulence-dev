/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.Data
import Mathlib.Tactic

/-!
# Absolute value of the exact source phase

Every oscillatory factor has modulus one. Only the explicit positive
case (c) factors remain after taking absolute values. In particular,
Step 2 is uniform in all time modulation parameters.
-/

@[expose] public section
set_option autoImplicit false

open Finset

namespace WaveTurbulence.SumintPar

/-- Exact modulus of the draft phase, including every case (c) multiplier. -/
theorem norm_phase {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : ℝ) (τ : D.S.TVar → ℝ) :
    ‖D.phase L γ δ η x r t τ‖ =
      ∏ i, if h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i then
        |τ (.inl ⟨i, ⟨1, by omega⟩⟩) - τ (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩))| ^ (1 - 3 * η)
      else 1 := by
  classical
  have hosc (θ : ℝ) : ‖Complex.exp ((Real.pi * θ : ℝ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  simp only [SumintDatum.phase, norm_mul, norm_prod, hosc, Finset.prod_const_one,
    one_mul, mul_one]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Real.rpow_nonneg (abs_nonneg _) _
  · exact norm_one

end WaveTurbulence.SumintPar
